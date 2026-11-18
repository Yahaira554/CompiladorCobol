import os
import re
import shutil
import tempfile
import tkinter as tk
from tkinter import filedialog, messagebox

# Paleta de colores (azul)
COLOR_FONDO_MENU = "#00C1BC"     # barra de menu
COLOR_FONDO_EDITOR = "#FDFDFD"   # area de codigo
COLOR_FONDO_CONSOLA = "#FDFDFD"   # area de salida/consola
COLOR_TEXTO = "#000000"          # texto claro
COLOR_ACENTO = "#900D0D"         # (bordes, seleccion)
COLOR_BORDE = "#900D0D" 

FUENTE_EDITOR = ("Consolas", 14)
FUENTE_CONSOLA = ("Consolas", 12)

TIPO_PIC_COBOL = {
    "int": "PIC 9(4)",        # numérico entero, hasta 4 dígitos
    "float": "PIC 9(4)V99",   # numérico con 2 decimales implícitos (V = punto decimal)
    "String": "PIC X(20)",    # alfanumérico, hasta 20 caracteres
}

# (menú Ayuda > Divisiones). Sustituyen a las librerías de C que había antes.
ORDEN_DIVISIONES_COBOL = [
    "IDENTIFICATION DIVISION",
    "ENVIRONMENT DIVISION",
    "DATA DIVISION",
    "PROCEDURE DIVISION",
]

# Esqueleto completo de un programa COBOL (menú Ayuda > Estructura del código)
ESTRUCTURA_COBOL = """IDENTIFICATION DIVISION.
       PROGRAM-ID. YOUR-PROGRAM-NAME.
       DATA DIVISION.
       FILE SECTION.
       WORKING-STORAGE SECTION.
       PROCEDURE DIVISION.
       MAIN-PROCEDURE.
            DISPLAY "Hello world"
            STOP RUN.
       END PROGRAM YOUR-PROGRAM-NAME.
"""
class TablaSimbolos(dict):
    """{NOMBRE: PIC}; en .valores guarda el VALUE inicial de cada variable."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.valores = {}


class ErrorSintactico(Exception):
    def __init__(self, mensaje, linea=None):
        super().__init__(mensaje)
        self.mensaje = mensaje
        self.linea = linea


class AnalizadorSintactico:
    # Verbos que inician una instruccion COBOL
    VERBOS = {
        "ACCEPT", "ADD", "CALL", "CLOSE", "COMPUTE", "CONTINUE", "DELETE",
        "DISPLAY", "DIVIDE", "EVALUATE", "EXIT", "GO", "IF", "INITIALIZE",
        "INSPECT", "MOVE", "MULTIPLY", "OPEN", "PERFORM", "READ", "REWRITE",
        "SEARCH", "SET", "START", "STOP", "STRING", "SUBTRACT", "UNSTRING",
        "WRITE",
    }
    # Palabras que nunca pueden usarse como operando de una condiciÃ³n
    NO_OPERANDO = VERBOS | {"ELSE", "END-IF", "THEN", "AND", "OR", "NOT", "IS",
                            "TO", "EQUAL", "GREATER", "LESS", "THAN", "WHEN", "OTHER",
                            "END-EVALUATE", "ALSO", "THRU", "THROUGH", "ANY", "VARYING",
                            "FROM", "BY", "UNTIL", "TIMES", "END-PERFORM", "GIVING", "INTO"}
    SIMBOLOS_REL = {"=", ">", "<", ">=", "<=", "<>"}
    SIMBOLOS_ARIT = {"+", "-", "*", "/", "**"}
    CLASES = {"NUMERIC", "ALPHABETIC", "ALPHABETIC-LOWER", "ALPHABETIC-UPPER"}

    def __init__(self, tokens, exigir_end_if=True, tabla_simbolos=None):
        # Valores iniciales (cláusula VALUE) que acompañan a la tabla de símbolos
        self.valores = getattr(tabla_simbolos, "valores", None)
        self.tiene_tabla = tabla_simbolos is not None
        self.tipos = {n.upper(): self._tipo_desde_pic(p)
                      for n, p in (tabla_simbolos or {}).items()}
        self.pics = {n.upper(): str(p) for n, p in (tabla_simbolos or {}).items()}
        self._comparaciones = []     
        self._cond_compuesta = False  
        self.errores_semanticos = []
        self.exigir_end_if = exigir_end_if
        # Acepta (valor, tipo) o (valor, tipo, linea)
        self.tokens = []
        for i, t in enumerate(tokens):
            valor, tipo = t[0], t[1]
            linea = t[2] if len(t) > 2 else i + 1
            self.tokens.append((valor, tipo, linea))
        # Nombres de párrafos de PROCEDURE DIVISION (etiqueta seguida de punto)
        self.parrafos = set()
        for k, t in enumerate(self.tokens[:-1]):
            if (t[1] == "IDENTIFICADOR" and self.tokens[k + 1][1] == "PERIODO"
                    and t[0].upper() not in self.VERBOS
                    and (k == 0 or self.tokens[k - 1][1] == "PERIODO")):
                self.parrafos.add(t[0].upper())
        self.pos = 0
        self.errores = []
        self.advertencias = []
        self._reiniciar_anidamiento()
        # Cada estructura que puede anidarse pasa por _anidada(), que lleva la pila
        self.verificadores = {
            "IF": lambda: self._anidada("IF", self.verificar_if),
            "DISPLAY": self.verificar_display,
            "MOVE": self.verificar_move,
            "EVALUATE": lambda: self._anidada("EVALUATE", self.verificar_evaluate),
            "PERFORM": lambda: self._anidada("PERFORM", self.verificar_perform),
        }

    # Utilidades para recorrer los tokens
    def _tok(self, desplazamiento=0):
        i = self.pos + desplazamiento
        return self.tokens[i] if 0 <= i < len(self.tokens) else None

    def _linea(self):
        t = self._tok() or (self.tokens[-1] if self.tokens else None)
        return t[2] if t else None

    def _avanzar(self):
        t = self._tok()
        self.pos += 1
        return t

    def _es(self, *palabras, desplazamiento=0):
        """True si el token es una de las palabras (no cuenta cadenas entre comillas)."""
        t = self._tok(desplazamiento)
        return bool(t) and t[1] != "CADENA" and t[0].upper() in palabras

    def _es_simbolo(self, *simbolos):
        t = self._tok()
        return bool(t) and t[1] in ("OPERADOR", "PARENTESIS") and t[0] in simbolos

    def _es_periodo(self):
        t = self._tok()
        return bool(t) and t[1] == "PERIODO"

    def _describir(self):
        t = self._tok()
        return f"'{t[0]}'" if t else "el final del programa"

    def _esperar_palabra(self, palabra, contexto=""):
        if not self._es(palabra):
            raise ErrorSintactico(
                f"Se esperaba '{palabra}'{contexto} y se encontrarón {self._describir()}.",
                self._linea())
        return self._avanzar()

    def _esperar_simbolo(self, simbolo, contexto=""):
        if not self._es_simbolo(simbolo):
            raise ErrorSintactico(
                f"Se esperaba '{simbolo}'{contexto} y se encontró {self._describir()}.",
                self._linea())
        return self._avanzar()

    # Punto de entrada
    def analizar(self):
        """Recorre todos los tokens y verifica cada IF que encuentre.
        Devuelve True si no hubo errores."""
        self.pos = 0
        self.errores = []
        self.errores_semanticos = []
        self.advertencias = []
        self._reiniciar_anidamiento()
        while self._tok() is not None:
            if self._es("IF"):
                self._verificar_con_recuperacion(self.verificadores["IF"])
            elif self._es("EVALUATE"):
                self._verificar_con_recuperacion(self.verificadores["EVALUATE"])
            elif self._es("PERFORM"):
                self._verificar_con_recuperacion(self.verificadores["PERFORM"])
            elif self._es("END-PERFORM"):
                self._registrar(ErrorSintactico("'END-PERFORM' sin un PERFORM que cerrar.", self._linea()))
                self._avanzar()
            elif self._es("WHEN", "END-EVALUATE"):
        
                self._registrar(ErrorSintactico(
                    f"'{self._tok()[0].upper()}' sin un EVALUATE que lo abra.", self._linea()))
                self._avanzar()
            elif self._es("ELSE"):
                self._registrar(ErrorSintactico("'ELSE' sin un IF que lo abra.", self._linea()))
                self._avanzar()
            elif self._es("END-IF"):
                self._registrar(ErrorSintactico("'END-IF' sin un IF que cerrar.", self._linea()))
                self._avanzar()
            elif self._es_instruccion_simple():
                inicio = self.pos          # instrucción fuera de un bloque: se registra (MOVE 0 TO X...)
                self._avanzar()
                while not self._fin_de_argumentos():
                    self._avanzar()
                self._sentencias.append((inicio, 0, self.tokens[inicio:self.pos]))
            else:
                self._avanzar()
        return not self.errores

    def _registrar(self, error):
        donde = f"ERROR EN LÍNEA {error.linea}: " if error.linea else "ERROR: "
        self.errores.append(f"{donde}{error.mensaje}")

    def _verificar_con_recuperacion(self, metodo):
        """Ejecuta un verificador; si falla, guarda el error y avanza hasta el
        siguiente punto para seguir analizando (modo pánico)."""
        try:
            metodo()
        except ErrorSintactico as e:
            self._registrar(e)
            while self._tok() is not None and not self._es_periodo():
                self._avanzar()
            if self._es_periodo():
                self._avanzar()

    # IF
    def verificar_if(self):
        linea_if = self._esperar_palabra("IF")[2]

        self._comparaciones = []
        self._cond_compuesta = False
        inicio_cond = self.pos
        self.verificar_condicion()
        cond = self.tokens[inicio_cond:self.pos]
        comparaciones = list(self._comparaciones)
        self._revisar_condicion(cond, comparaciones)                    # B3
        for ciclo in self._ciclos:                                      # B5
            ciclo["ifs"].append((linea_if, comparaciones, self._cond_compuesta))

        if self._es("THEN"):
            self._avanzar()

        self.verificar_bloque("despuÃ©s de la condición del IF", linea_if)

        if self._es("ELSE"):
            self._avanzar()
            self.verificar_bloque("despuÃ©s de ELSE", linea_if)
            if self._es("ELSE"):
                raise ErrorSintactico("El IF tiene más de un ELSE.", self._linea())

        if self._es("END-IF"):
            self._avanzar()
        elif self._es_periodo() and not self.exigir_end_if:
            # En COBOL el punto tambien cierra el IF (y los anidados)
            self.advertencias.append(
                f"  Línea {linea_if}: el IF se cerró con punto; se recomienda usar END-IF.")
        else:
            raise ErrorSintactico(
                f"Falta END-IF para cerrar el IF de la línea {linea_if}.", self._linea())

    def verificar_condicion(self):
        self._cond_and()
        while self._es("OR"):
            self._cond_compuesta = True
            self._avanzar()
            self._cond_and()

    def _cond_and(self):
        self._cond_not()
        while self._es("AND"):
            self._cond_compuesta = True
            self._avanzar()
            self._cond_not()

    def _cond_not(self):
        if self._es("NOT"):
            self._cond_compuesta = True
            self._avanzar()
        self._cond_primaria()

    def _cond_primaria(self):
        # Un "(" puede abrir una condicion agrupada  (A > 1)
        # o una expresion aritmetica                  (A + B) > 5
        # Se prueba primero como condicion y, si falla, se retrocede.
        if self._es_simbolo("("):
            guardado = self.pos
            n_comp, compuesta = len(self._comparaciones), self._cond_compuesta
            try:
                self._avanzar()
                self.verificar_condicion()
                self._esperar_simbolo(")", " para cerrar la condición")
                self._cond_compuesta = True
                return
            except ErrorSintactico:
                self.pos = guardado
                del self._comparaciones[n_comp:]
                self._cond_compuesta = compuesta
        self._comparacion()

    def _comparacion(self):
        inicio_izq = self.pos
        self._expresion()
        izq = self.tokens[inicio_izq:self.pos]
        if self._es("IS"):
            self._avanzar()
        negado = False
        if self._es("NOT"):
            self._avanzar()
            negado = True
        if self._es(*self.CLASES):          
            self._avanzar()
            self._cond_compuesta = True
            return
        op = self._operador_relacional()
        inicio_der = self.pos
        self._expresion()
        self._comparaciones.append((izq, op, self.tokens[inicio_der:self.pos], negado))

    def _operador_relacional(self):
        """Verifica el operador y devuelve su forma normalizada (=, >, <, >=, <=, <>)."""
        if self._es_simbolo(*self.SIMBOLOS_REL):
            return self._avanzar()[0]
        if self._es("EQUAL"):
            self._avanzar()
            if self._es("TO"):
                self._avanzar()
            return "="
        if self._es("GREATER", "LESS"):
            mayor = self._es("GREATER")
            self._avanzar()
            if self._es("THAN"):
                self._avanzar()
            igual = False
            # GREATER [THAN] OR EQUAL [TO]
            if self._es("OR") and self._es("EQUAL", desplazamiento=1):
                self._avanzar()
                self._avanzar()
                igual = True
                if self._es("TO"):
                    self._avanzar()
            if mayor:
                return ">=" if igual else ">"
            return "<=" if igual else "<"
        raise ErrorSintactico(
            "Se esperaba un operador relacional (=, >, <, >=, <=, <>, EQUAL TO, "
            f"GREATER THAN, LESS THAN) y se encontrÃ³ {self._describir()}.",
            self._linea())

    def _expresion(self):
        self._operando()
        while self._es_simbolo(*self.SIMBOLOS_ARIT):
            self._avanzar()
            self._operando()

    def _operando(self):
        if self._es_simbolo("+", "-"):      # signo unario
            self._avanzar()
        if self._es_simbolo("("):
            self._avanzar()
            self._expresion()
            self._esperar_simbolo(")", " en la expresión")
            return
        t = self._tok()
        if t is None or t[1] not in ("IDENTIFICADOR", "PALABRA_RESERVADA", "NUMERO", "CADENA") \
                or (t[1] != "CADENA" and t[0].upper() in self.NO_OPERANDO):
            raise ErrorSintactico(
                f"Se esperaba un operando (variable, número o cadena) y se encontró "
                f"{self._describir()}.", self._linea())
        self._avanzar()

    # Bloque de instrucciones (cuerpo del IF / ELSE)
    def verificar_bloque(self, contexto, linea_if):
        cantidad = 0
        while self._tok() is not None and not self._es("ELSE", "END-IF") \
                and not self._es_periodo():
            self.verificar_sentencia()
            cantidad += 1
        if cantidad == 0:
            raise ErrorSintactico(
                f"El IF de la línea {linea_if} no tiene instrucciones {contexto} "
                "(use CONTINUE si no debe hacer nada).", self._linea())

    def verificar_sentencia(self):
        t = self._tok()
        verbo = t[0].upper()
        if t[1] != "CADENA" and verbo in ("END-PERFORM", "END-EVALUATE", "WHEN", "END-IF", "ELSE"):
            self._error_cierre_cruzado(t)                                   # A1 / A2
        if t[1] == "CADENA" or verbo not in self.VERBOS:
            raise ErrorSintactico(
                f"Se esperaba una instrucción COBOL (DISPLAY, MOVE, ADD, IF...) "
                f"y se encontró {self._describir()}.", t[2])
        inicio = self.pos
        if verbo in self.verificadores:
            self.verificadores[verbo]()
        else:
            self.verificar_generica()
        if verbo not in ("IF", "EVALUATE", "PERFORM"):
            self._sentencias.append((inicio, len(self._pila), self.tokens[inicio:self.pos]))

    FIGURATIVAS_NUM = {"ZERO", "ZEROS", "ZEROES"}
    FIGURATIVAS_ALF = {"SPACE", "SPACES", "HIGH-VALUE", "HIGH-VALUES",
                       "LOW-VALUE", "LOW-VALUES", "QUOTE", "QUOTES"}

    @staticmethod
    def _tipo_desde_pic(pic):
        p = re.sub(r"^PIC(?:TURE)?\s+", "", str(pic).strip(), flags=re.IGNORECASE).upper()
        if re.match(r"^S?9", p):
            return "numerico"
        if re.match(r"^[XA]", p):
            return "alfanumerico"
        return None

    def _semantico(self, mensaje, linea):
        self.errores_semanticos.append(f"  Línea {linea}: {mensaje}")

    def _tipo_de_token(self, t):
        valor = t[0].upper()
        if t[1] == "NUMERO":
            return "numerico"
        if t[1] == "CADENA":
            return "alfanumerico"
        if valor in self.FIGURATIVAS_NUM:
            return "numerico"
        if valor in self.FIGURATIVAS_ALF:
            return "alfanumerico"
        return self.tipos.get(valor)

    def _revisar_declarada(self, t):
        """M1: una variable usada debe existir en WORKING-STORAGE."""
        valor = t[0].upper()
        if (self.tiene_tabla and t[1] in ("IDENTIFICADOR", "PALABRA_RESERVADA")
                and valor not in self.tipos
                and valor not in self.FIGURATIVAS_NUM | self.FIGURATIVAS_ALF
                and valor not in ("TRUE", "FALSE")):
            self._semantico(f"La variable '{t[0]}' no está declarada en WORKING-STORAGE.", t[2])

    def verificar_evaluate(self):
        linea_ev = self._esperar_palabra("EVALUATE")[2]

        sujetos = [self._sujeto_evaluate()]
        while self._es("ALSO"):
            self._avanzar()
            sujetos.append(self._sujeto_evaluate())

        # S2: entre el sujeto y el primer WHEN no puede haber nada
        if not self._es("WHEN"):
            if self._tok() is None or self._es_periodo():
                raise ErrorSintactico(
                    f"El EVALUATE de la línea {linea_ev} no tiene ningún WHEN.", self._linea())
            raise ErrorSintactico(
                f"Después del sujeto del EVALUATE se esperaba 'WHEN' y se encontró "
                f"{self._describir()} (toda instrucción debe ir dentro de un WHEN).",
                self._linea())

        vistos = {}
        hay_other = False
        while self._es("WHEN"):
            linea_when = self._avanzar()[2]
            if hay_other:   # S5
                raise ErrorSintactico(
                    "WHEN OTHER debe ser el último WHEN del EVALUATE "
                    "(equivale al default, que va siempre al final).", linea_when)
            if self._es("OTHER"):
                self._avanzar()
                hay_other = True
            else:
                claves = []
                for i, sujeto in enumerate(sujetos):
                    if i > 0:   # S7
                        if not self._es("ALSO"):
                            raise ErrorSintactico(
                                f"El EVALUATE tiene {len(sujetos)} sujetos (ALSO): cada WHEN "
                                f"debe traer {len(sujetos)} valores separados por ALSO.", linea_when)
                        self._avanzar()
                    claves.append(self._objeto_when(sujeto, linea_when))
                if self._es("ALSO"):
                    raise ErrorSintactico(
                        "El WHEN trae más valores (ALSO) que sujetos tiene el EVALUATE.", linea_when)
                if None not in claves:   # M3
                    clave = tuple(claves)
                    if clave in vistos:
                        self._semantico(
                            f"El WHEN repite el valor del WHEN de la línea {vistos[clave]}; "
                            "este nunca se ejecutaría.", linea_when)
                    else:
                        vistos[clave] = linea_when
            self._bloque_when(linea_when)

        if not hay_other:   # M5
            self.advertencias.append(
                f"  Línea {linea_ev}: el EVALUATE no tiene WHEN OTHER (como un switch sin default).")

        if self._es("END-EVALUATE"):   # S8
            self._avanzar()
        elif self._es_periodo() and not self.exigir_end_if:
            self.advertencias.append(
                f"  Línea {linea_ev}: el EVALUATE se cerró con punto; se recomienda END-EVALUATE.")
        else:
            raise ErrorSintactico(
                f"Falta END-EVALUATE para cerrar el EVALUATE de la línea {linea_ev}.",
                self._linea())

    def _sujeto_evaluate(self):
        # S1
        if self._tok() is None or self._es_periodo() or self._es("WHEN"):
            raise ErrorSintactico(
                "Falta el sujeto del EVALUATE (la variable o valor que se compara, "
                "como la variable de switch(variable)).", self._linea())
        if self._es("TRUE", "FALSE"):
            t = self._avanzar()
            return {"tipo": "booleano", "texto": t[0].upper()}
        inicio = self.pos
        self._expresion()
        usados = self.tokens[inicio:self.pos]
        if len(usados) == 1:
            t = usados[0]
            self._revisar_declarada(t)
            return {"tipo": self._tipo_de_token(t), "texto": t[0]}
        for t in usados:
            if t[1] in ("IDENTIFICADOR", "PALABRA_RESERVADA"):
                self._revisar_declarada(t)
        return {"tipo": "numerico", "texto": " ".join(t[0] for t in usados)}

    def _valor_when(self):
        signo = ""
        if self._es_simbolo("+", "-"):
            signo = self._avanzar()[0]
        t = self._tok()
        if (t is None or t[1] not in ("IDENTIFICADOR", "PALABRA_RESERVADA", "NUMERO", "CADENA")
                or (t[1] != "CADENA" and t[0].upper() in self.NO_OPERANDO)):
            raise ErrorSintactico(
                f"Se esperaba un valor (número, cadena o variable) y se encontró "
                f"{self._describir()}.", self._linea())
        self._avanzar()
        self._revisar_declarada(t)
        if t[1] == "NUMERO":
            valor = float(signo + t[0])
        elif t[1] == "CADENA":
            valor = t[0][1:-1]
        else:
            valor = t[0].upper()
        return {"tipo": self._tipo_de_token(t), "valor": valor, "texto": signo + t[0], "linea": t[2]}

    def _comprobar_tipo(self, sujeto, v):
        # M2
        if sujeto["tipo"] in ("numerico", "alfanumerico") and v["tipo"] in ("numerico", "alfanumerico") \
                and sujeto["tipo"] != v["tipo"]:
            self._semantico(
                f"Tipos incompatibles: el sujeto '{sujeto['texto']}' es {sujeto['tipo']} "
                f"y el valor {v['texto']} es {v['tipo']}.", v["linea"])

    def _objeto_when(self, sujeto, linea_when):
        """Verifica lo que va después de WHEN para un sujeto. Devuelve una clave
        (para detectar valores repetidos) o None si no aplica."""
        if self._es("ANY"):
            self._avanzar()
            return None
        if sujeto["tipo"] == "booleano":         
            if self._es("TRUE", "FALSE"):
                return (self._avanzar()[0].upper(),)
            self.verificar_condicion()
            return None

        t = self._tok()
        # S3
        if (t is None or self._es_periodo() or self._es("WHEN", "ALSO", "END-EVALUATE")
                or (t[1] != "CADENA" and t[0].upper() in self.VERBOS)):
            raise ErrorSintactico(
                "El WHEN no tiene valor (como un 'case:' sin valor). "
                "Use WHEN valor, WHEN valor THRU valor o WHEN OTHER.", linea_when)
        v1 = self._valor_when()
        self._comprobar_tipo(sujeto, v1)
        v2 = None
        if self._es("THRU", "THROUGH"):
            self._avanzar()
            t = self._tok()
            # S6
            if (t is None or self._es_periodo() or self._es("WHEN", "ALSO", "END-EVALUATE")
                    or (t[1] != "CADENA" and t[0].upper() in self.VERBOS)):
                raise ErrorSintactico("Falta el valor final después de THRU.", linea_when)
            v2 = self._valor_when()
            self._comprobar_tipo(sujeto, v2)
            if isinstance(v1["valor"], float) and isinstance(v2["valor"], float) \
                    and v1["valor"] > v2["valor"]:   # M4
                self._semantico(
                    f"Rango invertido: {v1['texto']} THRU {v2['texto']} "
                    "(el primer valor es mayor que el segundo).", linea_when)
        return (v1["valor"], v2["valor"] if v2 else None)

    def _bloque_when(self, linea_when):
        cantidad = 0
        while self._tok() is not None and not self._es("WHEN", "END-EVALUATE") \
                and not self._es_periodo():
            self.verificar_sentencia()
            cantidad += 1
        # WHEN seguido de otro WHEN es valido en COBOL (varios valores, mismas instrucciones)
        if cantidad == 0 and not self._es("WHEN"):   # S4
            raise ErrorSintactico(
                f"El WHEN de la línea {linea_when} no tiene instrucciones "
                "(use CONTINUE si no debe hacer nada).", linea_when)

    def verificar_perform(self):
        linea = self._esperar_palabra("PERFORM")[2]
        if self._es("FROM", "BY"):
            raise ErrorSintactico(
                "Falta VARYING y la variable de control. Forma correcta: "
                "PERFORM VARYING variable FROM inicio BY paso UNTIL condición.", self._linea())

        nombre = None
        t = self._tok()
        if (t is not None and t[1] == "IDENTIFICADOR" and t[0].upper() not in self.NO_OPERANDO
                and not self._es("TIMES", desplazamiento=1)):
            nombre = self._avanzar()
            if nombre[0].upper() not in self.parrafos:
                self._semantico(f"El párrafo '{nombre[0]}' no existe en PROCEDURE DIVISION.", nombre[2])
            if self._es("THRU", "THROUGH"):
                self._avanzar()
                t2 = self._tok()
                if t2 is None or t2[1] != "IDENTIFICADOR" or t2[0].upper() in self.NO_OPERANDO:
                    raise ErrorSintactico("Falta el párrafo final después de THRU.", self._linea())
                final = self._avanzar()
                if final[0].upper() not in self.parrafos:
                    self._semantico(f"El párrafo '{final[0]}' no existe en PROCEDURE DIVISION.", final[2])

        if self._es("VARYING"):
            self._perform_varying(linea, nombre)
            return
        if self._es("UNTIL"):
            self._avanzar()
            cond = self._condicion_until()
            comparaciones, compuesta = list(self._comparaciones), self._cond_compuesta
            if nombre is None:
                nivel, pos_cuerpo = len(self._pila), self.pos
                cuerpo = self._cuerpo_perform(linea)
                self._semantica_while(linea, cond, comparaciones, compuesta, cuerpo, pos_cuerpo, nivel)
            else:
                self._revisar_condicion(cond, comparaciones)
            return
        t = self._tok()
        if t is not None and (t[1] == "NUMERO"
                              or (t[1] == "IDENTIFICADOR" and self._es("TIMES", desplazamiento=1))):
            inicio = self.pos
            self._expresion()
            self._esperar_palabra("TIMES", " después de la cantidad de repeticiones")
            for u in self.tokens[inicio:self.pos - 1]:
                if u[1] == "CADENA":
                    self._semantico("La cantidad de repeticiones de TIMES debe ser numérica.", u[2])
                elif u[1] == "IDENTIFICADOR":
                    self._revisar_declarada(u)
                    if self.tipos.get(u[0].upper()) == "alfanumerico":
                        self._semantico(f"'{u[0]}' no es numérica y no puede usarse con TIMES.", u[2])
            if nombre is None:
                self._cuerpo_perform(linea)
            return
        if nombre is not None:
            return                                   # PERFORM PARRAFO.
        if self._tok() is None or self._es_periodo():
            raise ErrorSintactico("PERFORM sin párrafo, ciclo ni instrucciones.", linea)
        if not (t[1] != "CADENA" and t[0].upper() in self.VERBOS):
            raise ErrorSintactico(
                "Después de PERFORM se esperaba VARYING, UNTIL, '<n> TIMES', un nombre de "
                f"párrafo o una instrucción, y se encontró {self._describir()}.", self._linea())
        self._cuerpo_perform(linea)                  # PERFORM instrucciones END-PERFORM

    def _perform_varying(self, linea, nombre_parrafo):
        self._avanzar()                           

        # condiciÃ³n 1: variable de control + valor inicial 
        t = self._tok()
        if t is None or t[1] != "IDENTIFICADOR" or t[0].upper() in self.NO_OPERANDO:   # S1
            raise ErrorSintactico(
                "Falta la variable de control despuÃ©s de VARYING "
                "(condiciÃ³n 1 del for: la variable y su valor inicial).", self._linea())
        variable = self._avanzar()
        for externo in self._ciclos:                 # B4
            if externo["var"] == variable[0].upper():
                self._semantico(
                    f"La variable '{variable[0]}' ya es la variable de control del ciclo de la línea "
                    f"{externo['linea']}; los ciclos anidados deben usar variables distintas.",
                    variable[2])
        if not self._es("FROM"):                     # S2 / S5
            if self._es("BY", "UNTIL"):
                raise ErrorSintactico(
                    "Orden incorrecto: después de la variable debe ir FROM (inicio), luego "
                    "BY (incremento) y al final UNTIL (condición).", self._linea())
            raise ErrorSintactico(
                f"Falta FROM <valor inicial> después de '{variable[0]}' "
                "(condición 1 del for: inicialización).", self._linea())
        self._avanzar()
        desde = self._valor_clausula("el valor inicial después de FROM")

        # condición 3: incremento 
        if not self._es("BY"):                      
            if self._es("UNTIL"):
                raise ErrorSintactico(
                    "Falta BY <incremento> antes de UNTIL (condición 3 del for). "
                    "El orden es FROM, BY, UNTIL.", self._linea())
            raise ErrorSintactico("Falta BY <incremento> (condición 3 del for).", self._linea())
        self._avanzar()
        paso = self._valor_clausula("el incremento después de BY")


        if not self._es("UNTIL"):                  
            if self._es("FROM", "BY"):
                raise ErrorSintactico(
                    "Cláusula repetida o fuera de orden: el orden es FROM, BY, UNTIL.", self._linea())
            raise ErrorSintactico(
                "Falta UNTIL <condición> (condición 2 del for: cuándo termina el ciclo).",
                self._linea())
        self._avanzar()
        cond = self._condicion_until()
        comparaciones, compuesta = list(self._comparaciones), self._cond_compuesta

        self._semantica_varying(linea, variable, desde, paso, cond, comparaciones, compuesta)
        self._revisar_condicion(cond, comparaciones, declaradas=False)

        if nombre_parrafo is None:
            valores = None
            a, b = self._literal_numerico(desde), self._literal_numerico(paso)
            cumple = self._comparacion_simple(variable[0].upper(), comparaciones, compuesta)
            if a is not None and b not in (None, 0) and cumple is not None:
                valores = self._valores_del_ciclo(variable, a, b, cumple)
            ciclo = {"var": variable[0].upper(), "linea": linea, "valores": valores, "ifs": []}
            self._ciclos.append(ciclo)
            try:
                cuerpo = self._cuerpo_perform(linea)
            finally:
                self._ciclos.pop()
            self._advertir_cuerpo(variable, cuerpo)
            self._revisar_ifs_del_ciclo(ciclo, cuerpo)

    def _valor_clausula(self, descripcion):
        t = self._tok()
        if (t is None or self._es_periodo() or self._es("BY", "UNTIL", "FROM", "END-PERFORM")
                or (t[1] != "CADENA" and t[0].upper() in self.VERBOS)):
            raise ErrorSintactico(f"Falta {descripcion}.", self._linea())
        inicio = self.pos
        self._expresion()
        return self.tokens[inicio:self.pos]

    def _condicion_until(self):
        t = self._tok()
        if (t is None or self._es_periodo() or self._es("END-PERFORM")
                or (t[1] != "CADENA" and t[0].upper() in self.VERBOS)):
            raise ErrorSintactico("Falta la condición después de UNTIL.", self._linea())
        self._comparaciones = []
        self._cond_compuesta = False
        inicio = self.pos
        self.verificar_condicion()
        return self.tokens[inicio:self.pos]

    def _cuerpo_perform(self, linea):
        inicio = self.pos
        cantidad = 0
        # STOP RUN termina el programa: no puede quedar dentro de un PERFORM
        # inline sin que antes se cierre explícitamente con END-PERFORM.
        while (self._tok() is not None and not self._es("END-PERFORM") and not self._es_periodo()
               and not self._es("STOP", "ELSE", "END-IF", "WHEN", "END-EVALUATE")):
            self.verificar_sentencia()
            cantidad += 1
        cuerpo = self.tokens[inicio:self.pos]
        if cantidad == 0:
            raise ErrorSintactico(
                f"El PERFORM de la línea {linea} no tiene instrucciones en su cuerpo "
                "(use CONTINUE si no debe hacer nada).", self._linea())
        if self._es("ELSE", "END-IF", "WHEN", "END-EVALUATE"):
            self._error_cierre_cruzado(self._tok())
        if self._es("STOP"):
            token_stop = self._tok()
            raise ErrorSintactico(
                f"Falta END-PERFORM para cerrar el PERFORM iniciado en la línea {linea}. "
                f"Coloque END-PERFORM antes de STOP RUN (línea {token_stop[2]}).",
                token_stop[2])
        if self._es("END-PERFORM"):
            self._avanzar()
        else:
            token = self._tok()
            linea_error = token[2] if token else linea
            raise ErrorSintactico(
                f"Falta END-PERFORM para cerrar el PERFORM iniciado en la línea {linea}. "
                "Debe colocarse END-PERFORM antes del punto final o de la siguiente instrucción.",
                linea_error)
        return cuerpo

    # reglas semánticas del ciclo
    @staticmethod
    def _literal_numerico(toks):
        """Valor de [signo] NUMERO, o None si no es un literal numérico simple."""
        if len(toks) == 1 and toks[0][1] == "NUMERO":
            return float(toks[0][0])
        if (len(toks) == 2 and toks[0][1] == "OPERADOR" and toks[0][0] in ("+", "-")
                and toks[1][1] == "NUMERO"):
            return float(toks[1][0]) * (-1 if toks[0][0] == "-" else 1)
        return None

    def _es_variable(self, t):
        return (t[1] == "IDENTIFICADOR"
                and t[0].upper() not in self.NO_OPERANDO | self.CLASES
                | self.FIGURATIVAS_NUM | self.FIGURATIVAS_ALF)

    def _semantica_varying(self, linea, variable, desde, paso, cond, comparaciones, compuesta):
        nombre = variable[0].upper()
        informadas = set()

        # M1 / M2: la variable de control
        if self.tiene_tabla:
            if nombre not in self.tipos:
                self._semantico(
                    f"La variable de control '{variable[0]}' no está declarada en WORKING-STORAGE "
                    "(equivale a usar x en el for sin declarar 'int x').", variable[2])
                informadas.add(nombre)
            elif self.tipos[nombre] != "numerico":
                self._semantico(
                    f"La variable de control '{variable[0]}' debe ser numérica (PIC 9...).",
                    variable[2])

        # M2: FROM y BY numéricos; variables declaradas
        for etiqueta, toks in (("FROM", desde), ("BY", paso)):
            for t in toks:
                if t[1] == "CADENA" or t[0].upper() in self.FIGURATIVAS_ALF:
                    self._semantico(
                        f"El valor de {etiqueta} debe ser numérico y se encontró {t[0]}.", t[2])
                elif self._es_variable(t):
                    n = t[0].upper()
                    if self.tiene_tabla and n not in self.tipos:
                        if n not in informadas:
                            informadas.add(n)
                            self._semantico(
                                f"La variable '{t[0]}' no está declarada en WORKING-STORAGE.", t[2])
                    elif self.tipos.get(n) == "alfanumerico":
                        self._semantico(
                            f"'{t[0]}' no es numérica y no puede usarse en {etiqueta}.", t[2])
        for t in cond:
            if self._es_variable(t) and self.tiene_tabla:
                n = t[0].upper()
                if n not in self.tipos and n not in informadas:
                    informadas.add(n)
                    self._semantico(f"La variable '{t[0]}' no está declarada en WORKING-STORAGE.", t[2])

        # M3: BY 0
        a, b = self._literal_numerico(desde), self._literal_numerico(paso)
        if b == 0:
            self._semantico("BY 0: la variable nunca cambia y el ciclo no termina (ciclo infinito).", linea)

        # M4: UNTIL debe usar la variable de control
        if not any(t[1] != "CADENA" and t[0].upper() == nombre for t in cond):
            self._semantico(
                f"La condición UNTIL no usa la variable de control '{variable[0]}': "
                "el ciclo no depende de ella y podría no terminar nunca.", linea)
            return

        # M5 / M6: ¿termina el ciclo?  (solo con FROM y BY literales y una comparación simple)
        if b == 0 or a is None or b is None:
            return
        cumple = self._comparacion_simple(nombre, comparaciones, compuesta)
        if cumple is None:
            return
        self._evaluar_terminacion(variable, a, b, cumple, linea,
                                  f"FROM {a:g} BY {b:g}", "UNTIL")

    def _advertir_cuerpo(self, variable, cuerpo):
        nombre = variable[0].upper()
        for k, t in enumerate(cuerpo):
            if k > 0 and t[1] != "CADENA" and t[0].upper() == nombre:
                previo = cuerpo[k - 1]
                if previo[1] != "CADENA" and previo[0].upper() in (
                        "TO", "GIVING", "COMPUTE", "ACCEPT"):
                    self.advertencias.append(
                        f"  Línea {t[2]}: el cuerpo del ciclo modifica la variable de control "
                        f"'{variable[0]}'; esto puede alterar el número de repeticiones.")
                    return

   
    CIERRES = {"IF": "END-IF", "EVALUATE": "END-EVALUATE", "PERFORM": "END-PERFORM"}

    def _reiniciar_anidamiento(self):
        self._pila = []            # estructuras abiertas: [{etiqueta, verbo, linea}]
        self.estructuras = []      # mapa de anidamiento: (nivel, etiqueta, linea)
        self._ciclos = []          # ciclos VARYING abiertos (para analizar sus IF)
        self._sentencias = []      # (posición, nivel, tokens) de cada instrucción simple
        self.max_nivel = 0

    def _es_instruccion_simple(self):
        t = self._tok()
        return (t is not None and t[1] != "CADENA" and t[0].upper() in self.VERBOS
                and t[0].upper() not in ("IF", "EVALUATE", "PERFORM"))

    def _etiqueta_estructura(self, verbo):
        if verbo != "PERFORM":
            return verbo
        if self._es("VARYING", desplazamiento=1):
            return "PERFORM VARYING"
        if self._es("UNTIL", desplazamiento=1):
            return "PERFORM UNTIL"
        t, t2 = self._tok(1), self._tok(2)
        if t is not None and (t[1] == "NUMERO" or (t2 is not None and t2[0].upper() == "TIMES")):
            return "PERFORM n TIMES"
        if t is not None and t[1] == "IDENTIFICADOR" and t[0].upper() not in self.NO_OPERANDO:
            return "PERFORM pÃ¡rrafo"
        return "PERFORM"

    def _anidada(self, verbo, metodo):
        """Ejecuta el verificador de una estructura anidada mientras se analiza."""
        etiqueta = self._etiqueta_estructura(verbo)
        linea = self._linea()
        nivel = len(self._pila) + 1
        self.estructuras.append((nivel, etiqueta, linea))
        self.max_nivel = max(self.max_nivel, nivel)
        if nivel == 4:                                    
            self.advertencias.append(
                f"  Línea {linea}: {etiqueta} está en el nivel de anidamiento {nivel}; "
                "con tantos niveles el código es difícil de leer (considere un párrafo aparte).")
        self._pila.append({"etiqueta": etiqueta, "verbo": verbo, "linea": linea})
        try:
            metodo()
        finally:
            self._pila.pop()

    def _error_cierre_cruzado(self, token):
      
        propia = {"END-IF": "IF", "ELSE": "IF", "WHEN": "EVALUATE",
                  "END-EVALUATE": "EVALUATE", "END-PERFORM": "PERFORM"}[token[0].upper()]
        if not any(e["verbo"] == propia for e in self._pila):
            if self._pila:
                a = self._pila[-1]
                raise ErrorSintactico(
                    f"'{token[0]}' sobrante: no hay ningún {propia} abierto "
                    f"(la estructura abierta es el {a['etiqueta']} de la lí­nea {a['linea']}).",
                    token[2])
            raise ErrorSintactico(f"'{token[0]}' sin un {propia} que lo abra.", token[2])
        abierta = self._pila[-1]
        falta = self.CIERRES[abierta["verbo"]]
        raise ErrorSintactico(
            f"Estructura mal anidada: '{token[0]}' llegó antes de cerrar el "
            f"{abierta['etiqueta']} de la lí­nea {abierta['linea']}; falta {falta}.", token[2])

    # ---- análisis de lo que hace el cuerpo de un ciclo ----
    def _es_fin_de_instruccion(self, t):
        return (t[1] != "CADENA" and t[0].upper() in
                (self.VERBOS | {"ELSE", "END-IF", "WHEN", "END-EVALUATE", "END-PERFORM"})) \
            or t[1] == "PERIODO"

    def _destinos_de(self, verbo, seg):
        """Variables que modifica una instrucción simple (seg = sus argumentos)."""
        def nombres(toks):
            return {t[0].upper() for t in toks if self._es_variable(t)}
        palabras = [t[0].upper() if t[1] != "CADENA" else "" for t in seg]
        if verbo == "ACCEPT":
            return nombres(seg[:1])
        if verbo == "COMPUTE":
            for k, t in enumerate(seg):
                if t[1] == "OPERADOR" and t[0] == "=":
                    return nombres(seg[:k])
            return set()
        if "GIVING" in palabras:
            return nombres(seg[palabras.index("GIVING") + 1:])
        marca = {"MOVE": "TO", "ADD": "TO", "SUBTRACT": "FROM",
                 "MULTIPLY": "BY", "DIVIDE": "INTO"}.get(verbo)
        if marca and marca in palabras:
            return nombres(seg[palabras.index(marca) + 1:])
        return set()

    def _variables_modificadas(self, cuerpo):
    
        modif, desconocido, k = set(), False, 0
        while k < len(cuerpo):
            t = cuerpo[k]
            verbo = t[0].upper() if t[1] != "CADENA" else ""
            if verbo in ("ADD", "SUBTRACT", "MULTIPLY", "DIVIDE", "MOVE", "COMPUTE", "ACCEPT"):
                j = k + 1
                while j < len(cuerpo) and not self._es_fin_de_instruccion(cuerpo[j]):
                    j += 1
                modif |= self._destinos_de(verbo, cuerpo[k + 1:j])
                k = j
                continue
            if verbo == "VARYING" and k + 1 < len(cuerpo):
                modif.add(cuerpo[k + 1][0].upper())
            if verbo in ("CALL", "GO"):
                desconocido = True
            if verbo == "PERFORM" and k + 1 < len(cuerpo):
                sig = cuerpo[k + 1]
                if sig[1] == "IDENTIFICADOR" and sig[0].upper() in self.parrafos:
                    desconocido = True         
            k += 1
        return modif, desconocido

    @staticmethod
    def _invertir(op):
        return {">": "<", "<": ">", ">=": "<=", "<=": ">=", "=": "=", "<>": "<>"}[op]

    def _comparacion_simple(self, nombre, comparaciones, compuesta):
      
        if compuesta or len(comparaciones) != 1:
            return None
        izq, op, der, negado = comparaciones[0]
        if len(izq) == 1 and izq[0][0].upper() == nombre and izq[0][1] != "NUMERO":
            c = self._literal_numerico(der)
        elif len(der) == 1 and der[0][0].upper() == nombre and der[0][1] != "NUMERO":
            c = self._literal_numerico(izq)
            op = self._invertir(op)
        else:
            return None
        if c is None:
            return None
        pruebas = {">": lambda x: x > c, "<": lambda x: x < c, ">=": lambda x: x >= c,
                   "<=": lambda x: x <= c, "=": lambda x: x == c, "<>": lambda x: x != c}

        def cumple(x):
            r = pruebas[op](x)
            return (not r) if negado else r
        return cumple

    def _capacidad(self, nombre):
       
        pic = self.pics.get(nombre)
        if pic:
            numerico, enteros, _, _, _ = InterpreteCOBOL._analizar_pic(pic)
            if numerico and enteros:
                return 10 ** enteros, pic
        return None, pic

    def _evaluar_terminacion(self, variable, a, b, cumple, linea, inicio_txt, clausula):
     
        nombre = variable[0].upper()
        capacidad, pic = self._capacidad(nombre)

        def recorre(limitar):
            x = a
            if limitar and capacidad:
                x = abs(x) % capacidad
            if cumple(x):
                return "ya_cumple"
            for _ in range(100000):
                x = x + b
                if limitar and capacidad:
                    x = abs(x) % capacidad
                if cumple(x):
                    return "termina"
            return "infinito"

        resultado = recorre(True)
        if resultado == "ya_cumple":
            self.advertencias.append(
                f"  Lí­nea {linea}: la condición UNTIL ya se cumple con el valor inicial "
                f"({a:g}); el ciclo no se ejecutará ninguna vez.")
        elif resultado == "infinito":
            detalle = ""
            if capacidad and recorre(False) == "termina":
                detalle = (f" (la variable {variable[0]} es PIC {pic} y solo llega a "
                           f"{capacidad - 1}; al pasarse da la vuelta)")
            self._semantico(
                f"Ciclo infinito: con {inicio_txt} la condición {clausula} nunca se cumple"
                f"{detalle}.", linea)

    def _valores_del_ciclo(self, variable, a, b, cumple):
        """Valores que toma la variable de control dentro del cuerpo (o None si no es calculable)."""
        nombre = variable[0].upper()
        capacidad, _ = self._capacidad(nombre)
        x = abs(a) % capacidad if capacidad else a
        valores = []
        while not cumple(x):
            valores.append(x)
            if len(valores) > 5000 or b == 0:
                return None
            x = x + b
            if capacidad:
                x = abs(x) % capacidad
        return valores

    def _tipo_de_expresion(self, toks):
        if len(toks) == 1:
            return self._tipo_de_token(toks[0])
        return "numerico" if toks else None

    def _revisar_condicion(self, cond, comparaciones, informadas=None, declaradas=True):
        informadas = set() if informadas is None else informadas
        if self.tiene_tabla and declaradas:
            for t in cond:
                if self._es_variable(t):
                    n = t[0].upper()
                    if n not in self.tipos and n not in informadas:
                        informadas.add(n)
                        self._semantico(f"La variable '{t[0]}' no están declarada en WORKING-STORAGE.", t[2])
        for izq, op, der, negado in comparaciones:
            ti, td = self._tipo_de_expresion(izq), self._tipo_de_expresion(der)
            if ti and td and ti != td:
                a_txt = " ".join(t[0] for t in izq)
                b_txt = " ".join(t[0] for t in der)
                con_tilde = {"numerico": "numérico", "alfanumerico": "alfanumérico"}
                self._semantico(
                    f"Tipos incompatibles en la condición: {a_txt} es {con_tilde[ti]} "
                    f"y {b_txt} es {con_tilde[td]}.",
                    izq[0][2] if izq else None)

    def _pasos_literales(self, nombre, posicion_inicio, nivel):
        """Cambios literales y fijos que el cuerpo hace a `nombre`, o None si hay otros."""
        total, hay_paso = 0.0, False
        for pos, niv, toks in self._sentencias:
            if pos < posicion_inicio:
                continue
            palabras = [t[0].upper() if t[1] != "CADENA" else "" for t in toks]
            verbo = palabras[0] if palabras else ""
            if verbo not in ("ADD", "SUBTRACT", "MULTIPLY", "DIVIDE", "MOVE", "COMPUTE", "ACCEPT"):
                continue
            if nombre not in self._destinos_de(verbo, toks[1:]):
                continue
            if niv != nivel:
                return None                       
            lit = None
            if verbo == "ADD" and len(toks) >= 4 and palabras[2] == "TO" and palabras[3] == nombre \
                    and len(toks) == 4:
                lit = self._literal_numerico(toks[1:2])
            elif verbo == "SUBTRACT" and len(toks) == 4 and palabras[2] == "FROM" \
                    and palabras[3] == nombre:
                v = self._literal_numerico(toks[1:2])
                lit = None if v is None else -v
            elif verbo == "COMPUTE" and len(toks) == 6 and palabras[1] == nombre \
                    and palabras[3] == nombre and toks[4][0] in ("+", "-"):
                v = self._literal_numerico(toks[5:6])
                lit = None if v is None else (v if toks[4][0] == "+" else -v)
            if lit is None:
                return None
            total += lit
            hay_paso = True
        return total if hay_paso else None

    def _valor_inicial(self, nombre, posicion):
      
        for pos, niv, toks in reversed(self._sentencias):
            if pos >= posicion:
                continue
            palabras = [t[0].upper() if t[1] != "CADENA" else "" for t in toks]
            verbo = palabras[0] if palabras else ""
            if verbo not in ("ADD", "SUBTRACT", "MULTIPLY", "DIVIDE", "MOVE", "COMPUTE", "ACCEPT"):
                continue
            if nombre in self._destinos_de(verbo, toks[1:]):
                if verbo == "MOVE" and len(toks) == 4 and palabras[2] == "TO":
                    return self._literal_numerico(toks[1:2])
                return None
        if self.valores is not None and self.tipos.get(nombre) == "numerico":
            return self.valores.get(nombre, 0)
        return None

    def _semantica_while(self, linea, cond, comparaciones, compuesta, cuerpo, pos_cuerpo, nivel):
        self._revisar_condicion(cond, comparaciones)
        variables = []
        for t in cond:
            if self._es_variable(t) and t[0].upper() not in variables:
                variables.append(t[0].upper())
        if not variables:
            return
        modificadas, desconocido = self._variables_modificadas(cuerpo)
        if desconocido:
            return
        usadas = [v for v in variables if v in modificadas]
        if not usadas:                                              # B1
            self._semantico(
                f"El cuerpo del ciclo no modifica ninguna variable de la condición UNTIL "
                f"({', '.join(variables)}): falta el incremento (el x++ del while) y el ciclo "
                "no puede terminar.", linea)
            return
 
        if len(variables) == 1:
            nombre = variables[0]
            cumple = self._comparacion_simple(nombre, comparaciones, compuesta)
            if cumple is None:
                return
            paso = self._pasos_literales(nombre, pos_cuerpo, nivel)
            inicio = self._valor_inicial(nombre, pos_cuerpo)
            if paso is None or inicio is None:
                return
            if paso == 0:
                self._semantico("Los cambios del cuerpo se anulan entre sÃ­: la variable "
                                f"'{nombre}' no avanza y el ciclo no termina.", linea)
                return
            self._evaluar_terminacion(
                (nombre, "IDENTIFICADOR", linea), inicio, paso, cumple, linea,
                f"valor inicial {inicio:g} y cambio de {paso:+g} por vuelta", "UNTIL")


    def _revisar_ifs_del_ciclo(self, ciclo, cuerpo):
        modificadas, desconocido = self._variables_modificadas(cuerpo)
        if desconocido or ciclo["var"] in modificadas:
            return
        valores = ciclo["valores"]
        if not valores or len(valores) < 2:
            return
        for linea_if, comps, compuesta in ciclo["ifs"]:
            cumple = self._comparacion_simple(ciclo["var"], comps, compuesta)
            if cumple is None:
                continue
            resultados = [cumple(v) for v in valores]
            rango = f"{min(valores):g} a {max(valores):g}"
            if not any(resultados):
                self.advertencias.append(
                    f"  Línea {linea_if}: la condición del IF nunca se cumple dentro del ciclo de la "
                    f"línea {ciclo['linea']} ({ciclo['var']} va de {rango}); el IF nunca se ejecutará.")
            elif all(resultados):
                self.advertencias.append(
                    f"  Línea {linea_if}: la condición del IF siempre se cumple dentro del ciclo de la "
                    f"línea {ciclo['linea']} ({ciclo['var']} va de {rango}); el IF es innecesario.")

    # Instrucciones simples
    def _fin_de_argumentos(self):
        t = self._tok()
        return (t is None or self._es_periodo() or self._es("ELSE", "END-IF", "WHEN", "END-EVALUATE", "END-PERFORM")
                or (t[1] != "CADENA" and t[0].upper() in self.VERBOS))

    def verificar_display(self):
        linea = self._esperar_palabra("DISPLAY")[2]
        if self._fin_de_argumentos():
            raise ErrorSintactico("DISPLAY necesita al menos un valor que mostrar.", linea)
        while not self._fin_de_argumentos():
            self._avanzar()

    def verificar_move(self):
        linea = self._esperar_palabra("MOVE")[2]
        if self._fin_de_argumentos():
            raise ErrorSintactico("MOVE necesita un valor de origen.", linea)
        self._avanzar()                                  # origen
        self._esperar_palabra("TO", " en la instrucción MOVE")
        t = self._tok()
        if t is None or t[1] != "IDENTIFICADOR":
            raise ErrorSintactico(
                f"MOVE necesita una variable destino y se encontró {self._describir()}.",
                self._linea())
        self._avanzar()                                  # destino

    def verificar_generica(self):
       
        self._avanzar()
        while not self._fin_de_argumentos():
            self._avanzar()

RUTA_ARCHIVO_ACTUAL = {"path": None}

class ErrorEjecucion(Exception):
    pass


class InterpreteCOBOL:
    FIN_BLOQUE = ("ELSE", "END-IF", "WHEN", "END-EVALUATE", "END-PERFORM")
    LIMITE_CICLO = 100000      # proteccion contra ciclos infinitos
    CLASES = ("NUMERIC", "ALPHABETIC", "ALPHABETIC-LOWER", "ALPHABETIC-UPPER")

    def __init__(self, tokens, variables, pics, escribir):
        self.variables = variables      # {NOMBRE: valor actual}
        self.pics = pics                # {NOMBRE: PIC}
        self.escribir = escribir        # función que imprime en la consola
        self.hubo_salida = False
        self._truncados = set()
        self.detenido = False
        self.programa = []
        self.parrafos = {}              # {NOMBRE: [sentencias]}
        self.orden = []                 # párrafos en el orden en que aparecen
        self.t = self._cuerpo_procedure(tokens)
        self.i = 0

    @staticmethod
    def _cuerpo_procedure(tokens):
        ini = None
        for k in range(len(tokens) - 1):
            if tokens[k][0].upper() == "PROCEDURE" and tokens[k + 1][0].upper() == "DIVISION":
                ini = k + 2
                break
        if ini is None:
            return []
        while ini < len(tokens) and tokens[ini][1] != "PERIODO":
            ini += 1
        ini += 1
        fin = len(tokens)
        for k in range(ini, len(tokens) - 1):
            if tokens[k][0].upper() == "END" and tokens[k + 1][0].upper() == "PROGRAM":
                fin = k
                break
        return tokens[ini:fin]

    # Utilidades de lectura de tokens
    def _tok(self, d=0):
        k = self.i + d
        return self.t[k] if 0 <= k < len(self.t) else None

    def _es(self, *palabras, d=0):
        t = self._tok(d)
        return bool(t) and t[1] != "CADENA" and t[0].upper() in palabras

    def _simbolo(self, *simbolos):
        t = self._tok()
        return bool(t) and t[1] in ("OPERADOR", "PARENTESIS") and t[0] in simbolos

    def _periodo(self):
        t = self._tok()
        return bool(t) and t[1] == "PERIODO"

    def _fin_bloque(self):
        return self._tok() is None or self._periodo() or self._es(*self.FIN_BLOQUE)

    def _fin_args(self):
        t = self._tok()
        return (t is None or self._periodo() or self._es(*self.FIN_BLOQUE)
                or (t[1] != "CADENA" and t[0].upper() in AnalizadorSintactico.VERBOS))

    def _error(self, mensaje):
        t = self._tok()
        donde = f" (lÃ­nea {t[2]})" if t else ""
        raise ErrorEjecucion(mensaje + donde)

    # Parser: tokens -> lista de nodos
    def preparar(self):
        self.i = 0
        self.parrafos, self.orden = {}, []
        inicial = []
        actual = inicial
        while self._tok() is not None:
            if self._periodo():
                self.i += 1
                continue
            t = self._tok()
            sig = self._tok(1)
            if (t[1] == "IDENTIFICADOR" and sig and sig[1] == "PERIODO"
                    and t[0].upper() not in AnalizadorSintactico.VERBOS):
                nombre = t[0].upper()                   # nombre de párrafo:  INICIO.
                self.parrafos[nombre] = actual = []
                self.orden.append(nombre)
                self.i += 2
                continue
            if self._es(*self.FIN_BLOQUE):
                self.i += 1
                continue
            actual.append(self._sentencia())
        self.programa = list(inicial)
        for nombre in self.orden:
            self.programa.extend(self.parrafos[nombre])

    def _bloque(self):
        nodos = []
        while not self._fin_bloque():
            nodos.append(self._sentencia())
        return nodos

    def _sentencia(self):
        t = self._tok()
        if t[1] == "CADENA":
            self.i += 1
            return ("nada",)
        verbo = t[0].upper()
        metodos = {"DISPLAY": self._s_display, "MOVE": self._s_move, "ACCEPT": self._s_accept,
                   "IF": self._s_if, "EVALUATE": self._s_evaluate, "STOP": self._s_stop,
                   "GOBACK": self._s_stop, "CONTINUE": self._s_continue,
                   "PERFORM": self._s_perform, "COMPUTE": self._s_compute, "ADD": self._s_add,
                   "SUBTRACT": self._s_subtract, "MULTIPLY": self._s_multiply,
                   "DIVIDE": self._s_divide}
        if verbo in metodos:
            return metodos[verbo]()
        if verbo in AnalizadorSintactico.VERBOS:
            self.i += 1
            while not self._fin_args():
                self.i += 1
            return ("no_soportada", verbo)
        self.i += 1                              
        return ("nada",)

    def _s_display(self):
        self.i += 1
        operandos, salto = [], True
        while not self._fin_args():
            if self._es("WITH") and self._es("NO", d=1) and self._es("ADVANCING", d=2):
                self.i += 3
                salto = False
            elif self._es("NO") and self._es("ADVANCING", d=1):
                self.i += 2
                salto = False
            elif self._es("UPON"):
                self.i += 2
            else:
                operandos.append(self._operando())
        return ("display", operandos, salto)

    def _s_move(self):
        self.i += 1
        origen = self._expr()
        if not self._es("TO"):
            self._error("MOVE necesita 'TO'")
        self.i += 1
        destinos = []
        while not self._fin_args():
            destinos.append(self._tok()[0].upper())
            self.i += 1
        if not destinos:
            self._error("MOVE necesita una variable destino")
        return ("move", origen, destinos)

    def _s_accept(self):
        self.i += 1
        t = self._tok()
        if t is None or t[1] not in ("IDENTIFICADOR", "PALABRA_RESERVADA") or self._fin_args():
            self._error("ACCEPT necesita una variable")
        nombre = t[0].upper()
        self.i += 1
        if self._es("FROM"):
            while not self._fin_args():
                self.i += 1
            return ("no_soportada", "ACCEPT ... FROM")
        return ("accept", nombre)

    def _s_if(self):
        self.i += 1
        condicion = self._cond()
        if self._es("THEN"):
            self.i += 1
        entonces = self._bloque()
        sino = []
        if self._es("ELSE"):
            self.i += 1
            sino = self._bloque()
        if self._es("END-IF"):
            self.i += 1
        return ("if", condicion, entonces, sino)

    def _s_stop(self):
        self.i += 1
        if self._es("RUN"):
            self.i += 1
        return ("stop",)

    def _s_perform(self):
        self.i += 1
        nombre = hasta = None
        t = self._tok()
        if (t is not None and t[1] == "IDENTIFICADOR"
                and t[0].upper() not in AnalizadorSintactico.NO_OPERANDO
                and not self._es("TIMES", d=1)):
            nombre = t[0].upper()
            self.i += 1
            if self._es("THRU", "THROUGH"):
                self.i += 1
                hasta = self._tok()[0].upper()
                self.i += 1
        modo = ("una_vez",)
        t = self._tok()
        if self._es("VARYING"):
            self.i += 1
            variable = self._tok()[0].upper()
            self.i += 1
            if not self._es("FROM"):
                self._error("PERFORM VARYING necesita FROM")
            self.i += 1
            desde = self._expr()
            paso = ("lit", 1)
            if self._es("BY"):
                self.i += 1
                paso = self._expr()
            if not self._es("UNTIL"):
                self._error("PERFORM VARYING necesita UNTIL")
            self.i += 1
            modo = ("varying", variable, desde, paso, self._cond())
        elif self._es("UNTIL"):
            self.i += 1
            modo = ("until", self._cond())
        elif t is not None and (t[1] == "NUMERO"
                                or (t[1] == "IDENTIFICADOR" and self._es("TIMES", d=1))):
            veces = self._expr()
            if not self._es("TIMES"):
                self._error("Se esperaba TIMES")
            self.i += 1
            modo = ("veces", veces)
        cuerpo = None
        if nombre is None:
            cuerpo = self._bloque()
            if self._es("END-PERFORM,  END PROGRAM "):
                self.i += 1
        return ("perform", nombre, hasta, modo, cuerpo)

    #aritmÃ©tica 
    def _lista_operandos(self, *paradas):
        operandos = []
        while not self._fin_args() and not self._es(*paradas):
            if self._es("ROUNDED"):
                self.i += 1
            else:
                operandos.append(self._expr())
        return operandos

    def _lista_destinos(self, *paradas):
        destinos = []
        while not self._fin_args() and not self._es(*paradas):
            if self._es("ROUNDED"):
                self.i += 1
                continue
            destinos.append(self._tok()[0].upper())
            self.i += 1
        return destinos

    def _s_compute(self):
        self.i += 1
        destinos = []
        while not self._fin_args() and not self._simbolo("="):
            if self._es("ROUNDED"):
                self.i += 1
                continue
            destinos.append(self._tok()[0].upper())
            self.i += 1
        if not destinos or not self._simbolo("="):
            self._error("COMPUTE necesita 'variable = expresiÃ³n'")
        self.i += 1
        return ("compute", destinos, self._expr())

    def _s_add(self):
        self.i += 1
        operandos = self._lista_operandos("TO", "GIVING")
        tras_to, giving = [], []
        if self._es("TO"):
            self.i += 1
            tras_to = self._lista_operandos("GIVING")
        if self._es("GIVING"):
            self.i += 1
            giving = self._lista_destinos()
        if not operandos or not (tras_to or giving):
            self._error("ADD incompleto (use ADD valor TO variable)")
        return ("add", operandos, tras_to, giving)

    def _s_subtract(self):
        self.i += 1
        operandos = self._lista_operandos("FROM", "GIVING")
        if not self._es("FROM"):
            self._error("SUBTRACT necesita FROM")
        self.i += 1
        desde = self._lista_operandos("GIVING")
        giving = []
        if self._es("GIVING"):
            self.i += 1
            giving = self._lista_destinos()
        if not operandos or not desde:
            self._error("SUBTRACT incompleto")
        return ("sub", operandos, desde, giving)

    def _s_multiply(self):
        self.i += 1
        a = self._expr()
        if not self._es("BY"):
            self._error("MULTIPLY necesita BY")
        self.i += 1
        bs = self._lista_operandos("GIVING")
        giving = []
        if self._es("GIVING"):
            self.i += 1
            giving = self._lista_destinos()
        if not bs:
            self._error("MULTIPLY incompleto")
        return ("mul", a, bs, giving)

    def _s_divide(self):
        self.i += 1
        a = self._expr()
        if self._es("INTO"):
            modo = "INTO"
        elif self._es("BY"):
            modo = "BY"
        else:
            self._error("DIVIDE necesita INTO o BY")
        self.i += 1
        bs = self._lista_operandos("GIVING")
        giving = []
        if self._es("GIVING"):
            self.i += 1
            giving = self._lista_destinos()
        while not self._fin_args():         
            self.i += 1
        if not bs or (modo == "BY" and not giving):
            self._error("DIVIDE incompleto")
        return ("div", modo, a, bs, giving)

    def _s_continue(self):
        self.i += 1
        return ("nada",)

    def _s_evaluate(self):
        self.i += 1
        sujetos = [self._sujeto()]
        while self._es("ALSO"):
            self.i += 1
            sujetos.append(self._sujeto())
        ramas, pendientes = [], []
        while self._es("WHEN"):
            self.i += 1
            if self._es("OTHER"):
                self.i += 1
                pendientes.append("OTHER")
            else:
                objetos = [self._objeto(sujetos[0])]
                for suj in sujetos[1:]:
                    if self._es("ALSO"):
                        self.i += 1
                    objetos.append(self._objeto(suj))
                pendientes.append(objetos)
            bloque = self._bloque()
            # WHEN seguidos sin instrucciones comparten el bloque del Ãºltimo
            if bloque or not self._es("WHEN"):
                ramas.append((pendientes, bloque))
                pendientes = []
        if self._es("END-EVALUATE"):
            self.i += 1
        return ("evaluate", sujetos, ramas)

    def _sujeto(self):
        if self._es("TRUE"):
            self.i += 1
            return ("true",)
        if self._es("FALSE"):
            self.i += 1
            return ("false",)
        return ("expr", self._expr())

    def _objeto(self, sujeto):
        if self._es("ANY"):
            self.i += 1
            return ("any",)
        if sujeto[0] in ("true", "false"):
            if self._es("TRUE", "FALSE"):
                valor = self._es("TRUE")
                self.i += 1
                return ("bool", valor)
            return ("cond", self._cond())
        inicio = self._expr()
        if self._es("THRU", "THROUGH"):
            self.i += 1
            return ("rango", inicio, self._expr())
        return ("valor", inicio)

    #  condiciones
    def _cond(self):
        nodo = self._cond_and()
        while self._es("OR"):
            self.i += 1
            nodo = ("or", nodo, self._cond_and())
        return nodo

    def _cond_and(self):
        nodo = self._cond_not()
        while self._es("AND"):
            self.i += 1
            nodo = ("and", nodo, self._cond_not())
        return nodo

    def _cond_not(self):
        if self._es("NOT"):
            self.i += 1
            return ("not", self._cond_primaria())
        return self._cond_primaria()

    def _cond_primaria(self):
        if self._simbolo("("):
            guardado = self.i
            try:
                self.i += 1
                nodo = self._cond()
                if not self._simbolo(")"):
                    self._error("Falta ')'")
                self.i += 1
                return nodo
            except ErrorEjecucion:
                self.i = guardado
        return self._comparacion()

    def _comparacion(self):
        izq = self._expr()
        if self._es("IS"):
            self.i += 1
        negado = False
        if self._es("NOT"):
            negado = True
            self.i += 1
        if self._es(*self.CLASES):
            clase = self._tok()[0].upper()
            self.i += 1
            return ("clase", izq, clase, negado)
        op = self._op_rel()
        return ("cmp", izq, op, self._expr(), negado)

    def _op_rel(self):
        t = self._tok()
        if t and t[1] == "OPERADOR" and t[0] in ("=", ">", "<", ">=", "<=", "<>"):
            self.i += 1
            return t[0]
        if self._es("EQUAL"):
            self.i += 1
            if self._es("TO"):
                self.i += 1
            return "="
        if self._es("GREATER", "LESS"):
            mayor = self._es("GREATER")
            self.i += 1
            if self._es("THAN"):
                self.i += 1
            igual = False
            if self._es("OR") and self._es("EQUAL", d=1):
                self.i += 2
                igual = True
                if self._es("TO"):
                    self.i += 1
            if mayor:
                return ">=" if igual else ">"
            return "<=" if igual else "<"
        self._error("Se esperaba un operador relacional (=, >, <, >=, <=, <>)")

    # expresiones aritmÃ©ticas 
    def _expr(self):
        nodo = self._termino()
        while self._simbolo("+", "-"):
            op = self._tok()[0]
            self.i += 1
            nodo = ("bin", op, nodo, self._termino())
        return nodo

    def _termino(self):
        nodo = self._potencia()
        while self._simbolo("*", "/"):
            op = self._tok()[0]
            self.i += 1
            nodo = ("bin", op, nodo, self._potencia())
        return nodo

    def _potencia(self):
        nodo = self._unario()
        if self._simbolo("**"):
            self.i += 1
            return ("bin", "**", nodo, self._potencia())
        return nodo

    def _unario(self):
        if self._simbolo("-"):
            self.i += 1
            return ("neg", self._unario())
        if self._simbolo("+"):
            self.i += 1
            return self._unario()
        if self._simbolo("("):
            self.i += 1
            nodo = self._expr()
            if not self._simbolo(")"):
                self._error("Falta ')' en la expresión")
            self.i += 1
            return nodo
        return self._operando()

    def _operando(self):
        t = self._tok()
        if t is None:
            self._error("Se esperaba un valor")
        nombre = t[0].upper()
        if t[1] == "NUMERO":
            self.i += 1
            return ("lit", float(t[0]) if "." in t[0] else int(t[0]))
        if t[1] == "CADENA":
            self.i += 1
            return ("lit", t[0][1:-1])
        if nombre in ("ZERO", "ZEROS", "ZEROES"):
            self.i += 1
            return ("lit", 0)
        if nombre in ("SPACE", "SPACES", "HIGH-VALUE", "HIGH-VALUES", "LOW-VALUE", "LOW-VALUES"):
            self.i += 1
            return ("lit", " ")
        if nombre in ("QUOTE", "QUOTES"):
            self.i += 1
            return ("lit", '"')
        if (t[1] in ("IDENTIFICADOR", "PALABRA_RESERVADA")
                and nombre not in AnalizadorSintactico.NO_OPERANDO):
            self.i += 1
            return ("var", nombre)
        self._error(f"Valor no válido '{t[0]}'")

    # Evaluación
    def _emitir(self, texto):
        self.hubo_salida = True
        self.escribir(texto)

    @staticmethod
    def _es_num(x):
        return isinstance(x, (int, float)) and not isinstance(x, bool)

    def _num(self, v):
        if self._es_num(v):
            return v
        try:
            return float(str(v).strip())
        except ValueError:
            raise ErrorEjecucion(f"'{v}' no es un valor numérico.")

    def _val(self, e):
        tipo = e[0]
        if tipo == "lit":
            return e[1]
        if tipo == "var":
            if e[1] not in self.variables:
                raise ErrorEjecucion(f"La variable '{e[1]}' no está declarada.")
            return self.variables[e[1]]
        if tipo == "neg":
            return -self._num(self._val(e[1]))
        a, b = self._num(self._val(e[2])), self._num(self._val(e[3]))
        if e[1] == "+":
            return a + b
        if e[1] == "-":
            return a - b
        if e[1] == "*":
            return a * b
        if e[1] == "**":
            return a ** b
        if b == 0:
            raise ErrorEjecucion("División entre cero.")
        return a / b

    def _comparar(self, a, b):
        if self._es_num(a) and self._es_num(b):
            x, y = a, b
        elif self._es_num(a) or self._es_num(b):
            try:
                x, y = float(a), float(b)
            except (ValueError, TypeError):
                x, y = str(a).rstrip(), str(b).rstrip()
        else:
            x, y = str(a).rstrip(), str(b).rstrip()
        return (x > y) - (x < y)

    def _cumple(self, c):
        tipo = c[0]
        if tipo == "or":
            return self._cumple(c[1]) or self._cumple(c[2])
        if tipo == "and":
            return self._cumple(c[1]) and self._cumple(c[2])
        if tipo == "not":
            return not self._cumple(c[1])
        if tipo == "clase":
            v = self._val(c[1])
            if c[2] == "NUMERIC":
                r = self._es_num(v) or (isinstance(v, str) and v.strip().isdigit())
            else:
                s = str(v)
                r = all(ch.isalpha() or ch == " " for ch in s)
                if c[2] == "ALPHABETIC-LOWER":
                    r = r and s.replace(" ", "").islower()
                elif c[2] == "ALPHABETIC-UPPER":
                    r = r and s.replace(" ", "").isupper()
            return (not r) if c[3] else r
        cmp = self._comparar(self._val(c[1]), self._val(c[3]))
        r = {"=": cmp == 0, ">": cmp > 0, "<": cmp < 0,
             ">=": cmp >= 0, "<=": cmp <= 0, "<>": cmp != 0}[c[2]]
        return (not r) if c[4] else r

    @staticmethod
    def _analizar_pic(pic):
        p = re.sub(r"(.)\((\d+)\)", lambda m: m.group(1) * int(m.group(2)),
                   pic.replace(" ", "").upper())
        if re.match(r"^S?9", p):
            partes = p.lstrip("S").split("V")
            return True, len(partes[0]), (len(partes[1]) if len(partes) > 1 else 0), p.startswith("S"), 0
        return False, 0, 0, False, len(p)

    def _mostrar(self, v):
        if isinstance(v, float):
            return str(int(v)) if v == int(v) else str(v)
        return str(v)

    def _asignar(self, nombre, valor):
        if nombre not in self.variables:
            raise ErrorEjecucion(f"La variable '{nombre}' no está declarada.")
        pic = self.pics.get(nombre, "")
        numerico, enteros, decimales, con_signo, largo = self._analizar_pic(pic)
        if not numerico:
            texto = self._mostrar(valor)
            self.variables[nombre] = texto[:largo] if largo else texto
            return
        if self._es_num(valor):
            numero = valor
        else:
            try:
                numero = float(str(valor).strip())
            except ValueError:
                aviso = "entrada vacía" if not str(valor).strip() else f"'{valor}' no es numérico"
                self._emitir(f"[Aviso: {aviso}; {nombre} se guardó como 0.]\n")
                numero = 0
        negativo = numero < 0 and con_signo
        absoluto = abs(numero)
        parte_ent = int(absoluto)
        ent = parte_ent % (10 ** enteros) if enteros else parte_ent
        dec = int((absoluto - parte_ent) * 10 ** decimales + 1e-9) / 10 ** decimales if decimales else 0
        resultado = ent + dec if decimales else ent
        if ent != parte_ent and nombre not in self._truncados:
            self._truncados.add(nombre)      # se avisa una sola vez por variable
            self._emitir(f"[Aviso: {nombre} es PIC {pic} y solo guarda {enteros} dígitos); "
                         f"el valor {parte_ent} se truncó a {ent}. "
                         "No se volverá a avisar para esta variable.]\n")
        self.variables[nombre] = -resultado if negativo else resultado

    # Ejecución (generador)
    def ejecutar(self):
        self.detenido = False
        yield from self._ejecutar_bloque(self.programa)

    def _ejecutar_bloque(self, nodos):
        for nodo in nodos:
            if self.detenido:
                return
            yield from self._ejecutar_nodo(nodo)

    def _ejecutar_nodo(self, n):
        tipo = n[0]
        if tipo == "display":
            texto = "".join(self._mostrar(self._val(op)) for op in n[1])
            self._emitir(texto + ("\n" if n[2] else ""))
        elif tipo == "move":
            valor = self._val(n[1])
            for destino in n[2]:
                self._asignar(destino, valor)
        elif tipo == "accept":
            if n[1] not in self.variables:
                raise ErrorEjecucion(f"La variable '{n[1]}' no está declarada.")
            texto = yield (n[1], self.pics.get(n[1], ""))      # espera lo que escriba el usuario
            self._asignar(n[1], texto)
        elif tipo == "if":
            if self._cumple(n[1]):
                yield from self._ejecutar_bloque(n[2])
            elif n[3]:
                yield from self._ejecutar_bloque(n[3])
        elif tipo == "evaluate":
            yield from self._ejecutar_evaluate(n)
        elif tipo == "perform":
            yield from self._ejecutar_perform(n)
        elif tipo in ("compute", "add", "sub", "mul", "div"):
            self._ejecutar_aritmetica(n)
        elif tipo == "stop":
            self.detenido = True
        elif tipo == "no_soportada":
            self._emitir(f"[Aviso: la instrucción '{n[1]}' aún no está soportada por el "
                         "simulador; se omite.]\n")

    def _ejecutar_evaluate(self, n):
        _, sujetos, ramas = n
        valores = [None if s[0] in ("true", "false") else self._val(s[1]) for s in sujetos]
        for grupos, bloque in ramas:
            if any(g == "OTHER" or self._coincide(g, sujetos, valores) for g in grupos):
                yield from self._ejecutar_bloque(bloque)
                return

    # ---- PERFORM ----
    def _pasada(self, nombre, hasta, cuerpo):
        if nombre is None:
            yield from self._ejecutar_bloque(cuerpo)
        else:
            yield from self._ejecutar_parrafos(nombre, hasta)

    def _ejecutar_parrafos(self, nombre, hasta):
        if nombre not in self.parrafos or (hasta and hasta not in self.parrafos):
            raise ErrorEjecucion(f"El párrafo '{hasta if hasta and hasta not in self.parrafos else nombre}' no existe.")
        i0 = self.orden.index(nombre)
        i1 = self.orden.index(hasta) if hasta else i0
        for p in self.orden[i0:i1 + 1]:
            yield from self._ejecutar_bloque(self.parrafos[p])

    def _ejecutar_perform(self, n):
        _, nombre, hasta, modo, cuerpo = n
        tipo = modo[0]
        if tipo == "una_vez":
            yield from self._pasada(nombre, hasta, cuerpo)
        elif tipo == "veces":
            for _ in range(int(self._num(self._val(modo[1])))):
                if self.detenido:
                    return
                yield from self._pasada(nombre, hasta, cuerpo)
        else:
            variable = paso = None
            if tipo == "varying":
                _, variable, desde, paso, cond = modo
                self._asignar(variable, self._val(desde))          # condición 1: inicio
            else:
                cond = modo[1]
            repeticiones = 0
            while not self._cumple(cond):                          # condición 2: UNTIL
                if self.detenido:
                    return
                yield from self._pasada(nombre, hasta, cuerpo)
                if self.detenido:
                    return
                if variable is not None:                           # condición 3: BY
                    self._asignar(variable, self._num(self._val(("var", variable)))
                                  + self._num(self._val(paso)))
                repeticiones += 1
                if repeticiones >= self.LIMITE_CICLO:
                    raise ErrorEjecucion(
                        f"El ciclo superó las {self.LIMITE_CICLO} repeticiones "
                        "(posible ciclo infinito).")

    # ---- aritmética ----
    @staticmethod
    def _destino(e):
        if e[0] != "var":
            raise ErrorEjecucion("Se esperaba una variable como destino.")
        return e[1]

    @staticmethod
    def _dividir(x, y):
        if y == 0:
            raise ErrorEjecucion("División entre cero.")
        return x / y

    def _ejecutar_aritmetica(self, n):
        tipo = n[0]
        num, val = self._num, self._val
        if tipo == "compute":
            valor = val(n[2])
            for d in n[1]:
                self._asignar(d, valor)
        elif tipo == "add":
            _, ops, tras, giving = n
            total = sum(num(val(o)) for o in ops)
            if giving:
                base = sum(num(val(e)) for e in tras)
                for g in giving:
                    self._asignar(g, total + base)
            else:
                for e in tras:
                    self._asignar(self._destino(e), num(val(e)) + total)
        elif tipo == "sub":
            _, ops, desde, giving = n
            total = sum(num(val(o)) for o in ops)
            if giving:
                for g in giving:
                    self._asignar(g, num(val(desde[0])) - total)
            else:
                for e in desde:
                    self._asignar(self._destino(e), num(val(e)) - total)
        elif tipo == "mul":
            _, a, bs, giving = n
            x = num(val(a))
            if giving:
                for g in giving:
                    self._asignar(g, x * num(val(bs[0])))
            else:
                for b in bs:
                    self._asignar(self._destino(b), num(val(b)) * x)
        else:   # div
            _, modo, a, bs, giving = n
            x = num(val(a))
            if modo == "BY":
                for g in giving:
                    self._asignar(g, self._dividir(x, num(val(bs[0]))))
            elif giving:
                for g in giving:
                    self._asignar(g, self._dividir(num(val(bs[0])), x))
            else:
                for b in bs:
                    self._asignar(self._destino(b), self._dividir(num(val(b)), x))

    def _coincide(self, objetos, sujetos, valores):
        for obj, suj, valor in zip(objetos, sujetos, valores):
            if obj[0] == "any":
                continue
            if suj[0] in ("true", "false"):
                r = obj[1] if obj[0] == "bool" else self._cumple(obj[1])
                if r != (suj[0] == "true"):
                    return False
            elif obj[0] == "valor":
                if self._comparar(valor, self._val(obj[1])) != 0:
                    return False
            else:   # rango
                if not (self._comparar(valor, self._val(obj[1])) >= 0
                        and self._comparar(valor, self._val(obj[2])) <= 0):
                    return False
        return True


class CompiladorApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Compilador - Diseño de Compilador")
        self.root.geometry("900x650")
        self.root.minsize(820, 500)
        self.root.configure(bg=COLOR_FONDO_MENU)

        self.root.report_callback_exception = self._reportar_excepcion

        self._gen = None                 # ejecución en curso (generador del intérprete)
        self._interprete = None
        self._al_terminar = None
        self._esperando_entrada = False  # True mientras la consola espera un valor (ACCEPT)
        self._contadores_variables = {}  # cuenta variables insertadas por tipo, para no repetir nombres
        self.palabras_reservadas_activas = tk.BooleanVar(value=True)

        self._crear_menu()
        # Paneles redimensionables: el usuario puede arrastrar el separador
        # entre el editor y la consola, como en un IDE.
        self.panel_principal = tk.PanedWindow(
            self.root, orient=tk.VERTICAL, sashwidth=9, sashrelief=tk.RAISED,
            sashpad=2, sashcursor="sb_v_double_arrow", showhandle=True,
            opaqueresize=True, bg=COLOR_BORDE, bd=0, relief=tk.FLAT
        )
        self.panel_principal.pack(fill="both", expand=True, padx=8, pady=8)
        self._crear_editor()
        self._crear_consola()
        self._crear_atajos()
        self._inicializar_historial_temporal()
        self._ventana_buscar = None  # ventana de Buscar y Reemplazar (se crea al abrirla)

        self.root.protocol("WM_DELETE_WINDOW", self.cerrar_app)

        self._escribir_consola("Compilador listo. Escriba su código en el área superior.\n")

    # Construcción de la interfaz
    def _crear_menu(self):
        menubar = tk.Menu(self.root, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                           activebackground=COLOR_ACENTO, activeforeground="white")

        # Archivo
        menu_archivo = tk.Menu(menubar, tearoff=0, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                                activebackground=COLOR_ACENTO, activeforeground="white")
        menu_archivo.add_command(label="Abrir", accelerator="Ctrl+A", command=self.abrir_archivo)
        menu_archivo.add_command(label="Guardar", accelerator="Ctrl+G", command=self.guardar_archivo)
        menu_archivo.add_command(label="Guardar como...", accelerator="Ctrl+Shift+S", command=self.guardar_como)
        menu_archivo.add_command(label="Limpiar pantalla", accelerator="Ctrl+P", command=self.limpiar_pantalla)
        menu_archivo.add_separator()
        menu_archivo.add_command(label="Cerrar", accelerator="Ctrl+Q", command=self.cerrar_app)
        menubar.add_cascade(label="Archivo", menu=menu_archivo)

        # Editar 
        menu_editar = tk.Menu(menubar, tearoff=0, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                               activebackground=COLOR_ACENTO, activeforeground="white")
        menu_editar.add_command(label="Deshacer", accelerator="Ctrl+Z", command=self.deshacer)
        menu_editar.add_command(label="Rehacer", accelerator="Ctrl+Y", command=self.rehacer)
        menu_editar.add_separator()
        menu_editar.add_command(label="Cortar", command=lambda: self.texto.event_generate("<<Cut>>"))
        menu_editar.add_command(label="Copiar", command=lambda: self.texto.event_generate("<<Copy>>"))
        menu_editar.add_command(label="Pegar", command=lambda: self.texto.event_generate("<<Paste>>"))
        menu_editar.add_separator()
        menu_editar.add_command(label="Buscar y Reemplazar...", accelerator="Ctrl+F",
                                 command=self.abrir_buscar_reemplazar)
        menubar.add_cascade(label="Editar", menu=menu_editar)

        #Ejecutar 
        menu_ejecutar = tk.Menu(menubar, tearoff=0, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                                 activebackground=COLOR_ACENTO, activeforeground="white")
        menu_ejecutar.add_command(label="Compilar y ejecutar", accelerator="F5", command=self.compilar_y_ejecutar)
        menubar.add_cascade(label="Ejecutar", menu=menu_ejecutar)

        # Compiladores 
        menu_compiladores = tk.Menu(menubar, tearoff=0, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                                     activebackground=COLOR_ACENTO, activeforeground="white",
                                     disabledforeground="#7a8ba8")
        menu_compiladores.add_command(label="Analisis Lexico", accelerator="Alt+L", command=self.analisis_lexico)
        menu_compiladores.add_command(label="Analisis Sintactico", accelerator="Alt+S", command=self.analisis_sintactico)
        menu_compiladores.add_command(label="Sintactico: Condicional IF", accelerator="Alt+I", command=self.analisis_condicional_if)
        menu_compiladores.add_command(label="Switch (EVALUATE): Sintactico y Semantico", accelerator="Alt+W", command=self.analisis_condicional_switch)
        menu_compiladores.add_command(label="For (PERFORM VARYING): Sintactico y Semantico", accelerator="Alt+F", command=self.analisis_iteracion_for)
        menu_compiladores.add_command(label="Estructuras anidadas (while + if): Sintactico y Semantico", accelerator="Alt+N", command=self.analisis_estructuras_anidadas)
        menu_compiladores.add_command(label="Analisis Semantico", accelerator="Ctrl+S", command=self.analisis_semantico)
        menu_compiladores.add_command(label="Generacion Codigo Intermedio", state="disabled")
        menu_compiladores.add_command(label="Codigo Objeto", state="disabled")
        menubar.add_cascade(label="Compiladores", menu=menu_compiladores)

        # Ayuda 
        menu_ayuda = tk.Menu(menubar, tearoff=0, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                              activebackground=COLOR_ACENTO, activeforeground="white")

        menu_divisiones = tk.Menu(menu_ayuda, tearoff=0, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                                   activebackground=COLOR_ACENTO, activeforeground="white")
        for division in ORDEN_DIVISIONES_COBOL:
            menu_divisiones.add_command(label=division, command=lambda d=division: self.insertar_division(d))
        menu_ayuda.add_cascade(label="Divisiones", menu=menu_divisiones)
        menu_ayuda.add_separator()
        menu_ayuda.add_command(label="Estructura del código", command=self.insertar_estructura_cobol)
        menu_ayuda.add_checkbutton(
            label="Palabras reservadas",
            variable=self.palabras_reservadas_activas,
            command=self.alternar_palabras_reservadas
        )
        menubar.add_cascade(label="Ayuda", menu=menu_ayuda)

        # Variables 
        menu_variables = tk.Menu(menubar, tearoff=0, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                                  activebackground=COLOR_ACENTO, activeforeground="white")
        menu_tipos = tk.Menu(menu_variables, tearoff=0, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                              activebackground=COLOR_ACENTO, activeforeground="white")
        for tipo in ["int", "float", "String"]:
            menu_tipos.add_command(label=tipo, command=lambda t=tipo: self.insertar_variable(t))
        menu_variables.add_cascade(label="Tipos", menu=menu_tipos)
        menubar.add_cascade(label="Variables", menu=menu_variables)

        self.root.config(menu=menubar)

    def _crear_editor(self):
        marco = tk.Frame(self.root, bg=COLOR_BORDE, padx=2, pady=2)
        self.panel_principal.add(marco, minsize=180, stretch="always")

        self.numeros_linea = tk.Text(marco, width=5, padx=6, takefocus=0,
            borderwidth=0, background="#EAEAEA", foreground="#666666",
            state="disabled", font=FUENTE_EDITOR, wrap="none")
        self.numeros_linea.pack(side="left", fill="y")
        self.texto = tk.Text(marco, bg=COLOR_FONDO_EDITOR, fg=COLOR_TEXTO,
            insertbackground=COLOR_TEXTO, font=FUENTE_EDITOR,
            undo=False, wrap="none", yscrollcommand=self._sincronizar_numeros)
        self.texto.tag_configure("linea_error", foreground="#D32F2F", background="#FCE8E6")
        barra_editor = tk.Scrollbar(marco, orient="vertical", command=self.texto.yview)
        self.texto.configure(yscrollcommand=lambda primero, ultimo: (
            self._sincronizar_numeros(primero, ultimo), barra_editor.set(primero, ultimo)))
        self.texto.pack(side="left", fill="both", expand=True)
        barra_editor.pack(side="right", fill="y")
        self.texto.bind("<KeyRelease>", self._al_modificar_codigo)
        self.texto.bind("<MouseWheel>", self._actualizar_numeros)
        self.texto.bind("<Button-1>", self._actualizar_numeros)
        self._actualizar_numeros()

    def _al_modificar_codigo(self, event=None):
        self._actualizar_numeros(event)
        self.texto.tag_remove("linea_error", "1.0", "end")

    def _sincronizar_numeros(self, primero, ultimo):
        self.numeros_linea.yview_moveto(primero)
        self._actualizar_numeros()

    def _actualizar_numeros(self, event=None):
        if not hasattr(self, "numeros_linea"):
            return
        total = int(self.texto.index("end-1c").split(".")[0])
        contenido = "\n".join(str(i) for i in range(1, total + 1))
        self.numeros_linea.config(state="normal")
        self.numeros_linea.delete("1.0", "end")
        self.numeros_linea.insert("1.0", contenido)
        self.numeros_linea.config(state="disabled")
        self.numeros_linea.yview_moveto(self.texto.yview()[0])

    def _crear_consola(self):
        marco = tk.Frame(self.root, bg=COLOR_BORDE, padx=2, pady=2)
        self.panel_principal.add(marco, minsize=110, height=190, stretch="always")

        tk.Label(marco, text="Consola de salida", bg=COLOR_FONDO_CONSOLA, fg=COLOR_ACENTO,
                 anchor="w", font=("Consolas", 9, "bold")).pack(fill="x")

        zona_consola = tk.Frame(marco, bg=COLOR_FONDO_CONSOLA)
        zona_consola.pack(fill="both", expand=True)
        self.consola = tk.Text(zona_consola, height=8, bg=COLOR_FONDO_CONSOLA, fg=COLOR_TEXTO,
                                font=FUENTE_CONSOLA, state="disabled", wrap="word",
                                insertbackground=COLOR_TEXTO, borderwidth=0,
                                padx=8, pady=6)
        self.consola.tag_configure("error", foreground="#D32F2F")
        barra_consola = tk.Scrollbar(zona_consola, orient="vertical", command=self.consola.yview)
        self.consola.configure(yscrollcommand=barra_consola.set)
        self.consola.pack(side="left", fill="both", expand=True)
        barra_consola.pack(side="right", fill="y")
        # La consola es de solo lectura salvo cuando el programa llega a un ACCEPT
        self.consola.bind("<Return>", self._enviar_entrada)
        self.consola.bind("<KP_Enter>", self._enviar_entrada)
        self.consola.bind("<Key>", self._filtrar_tecla)

    def _crear_atajos(self):
        self.root.bind("<Control-a>", lambda e: self.abrir_archivo())
        self.root.bind("<Control-g>", lambda e: self.guardar_archivo())
        self.root.bind("<Control-Shift-s>", lambda e: self.guardar_como())
        self.root.bind("<Control-p>", lambda e: self.limpiar_pantalla())
        self.root.bind("<Control-q>", lambda e: self.cerrar_app())
        self.root.bind("<Alt-l>", lambda e: self.analisis_lexico())
        self.root.bind("<Alt-s>", lambda e: self.analisis_sintactico())
        self.root.bind("<Alt-i>", lambda e: self.analisis_condicional_if())
        self.root.bind("<Alt-w>", lambda e: self.analisis_condicional_switch())
        self.root.bind("<Alt-f>", lambda e: self.analisis_iteracion_for())
        self.root.bind("<Alt-n>", lambda e: self.analisis_estructuras_anidadas())
        self.root.bind("<Control-s>", lambda e: self.analisis_semantico())
        self.root.bind("<F5>", lambda e: self.compilar_y_ejecutar())
        self.root.bind("<Control-f>", lambda e: self.abrir_buscar_reemplazar())
        for widget in (self.texto, self.root):
            widget.bind("<Control-z>", self.deshacer)
            widget.bind("<Control-Z>", self.deshacer)
            widget.bind("<Control-y>", self.rehacer)
            widget.bind("<Control-Y>", self.rehacer)
        self.texto.bind("<KeyRelease>", self._programar_snapshot, add="+")
        self.texto.bind("<<Paste>>", lambda e: self.root.after(50, self._guardar_snapshot))

    def _reportar_excepcion(self, exc, val, tb):
        import traceback
        detalle = "".join(traceback.format_exception(exc, val, tb))
        self._escribir_consola(f"\n[ERROR interno] {val}\n{detalle}\n")
    # Deshacer / Rehacer usando archivos temporales
    def _inicializar_historial_temporal(self):
   
        self.dir_temporal = tempfile.mkdtemp(prefix="compilador_historial_")
        self.historial_archivos = []   
        self.indice_historial = -1
        self._id_debounce = None       
        self._restaurando = False      
        self._guardar_snapshot(forzar=True)  

    def _nuevo_archivo_temporal(self):
        descriptor, ruta = tempfile.mkstemp(suffix=".snap", dir=self.dir_temporal)
        os.close(descriptor)
        return ruta

    def _programar_snapshot(self, event=None):
        if self._restaurando:
            return
        if self._id_debounce is not None:
            self.root.after_cancel(self._id_debounce)
        self._id_debounce = self.root.after(600, self._guardar_snapshot)

    def _guardar_snapshot(self, forzar=False):
        self._id_debounce = None
        contenido_actual = self.texto.get("1.0", "end-1c")

        if not forzar and self.historial_archivos:
            with open(self.historial_archivos[self.indice_historial], "r", encoding="utf-8") as f:
                if f.read() == contenido_actual:
                    return  

        del self.historial_archivos[self.indice_historial + 1:]

        ruta = self._nuevo_archivo_temporal()
        with open(ruta, "w", encoding="utf-8") as f:
            f.write(contenido_actual)
        self.historial_archivos.append(ruta)
        self.indice_historial = len(self.historial_archivos) - 1

        LIMITE_HISTORIAL = 100
        if len(self.historial_archivos) > LIMITE_HISTORIAL:
            antiguo = self.historial_archivos.pop(0)
            try:
                os.remove(antiguo)
            except OSError:
                pass
            self.indice_historial -= 1

    def deshacer(self, event=None):
        if self._id_debounce is not None:
            self.root.after_cancel(self._id_debounce)
            self._id_debounce = None
            self._guardar_snapshot()  
        if self.indice_historial <= 0:
            self._escribir_consola("No hay más acciones para deshacer.\n")
            return "break"
        self.indice_historial -= 1
        self._cargar_snapshot(self.indice_historial)
        return "break"

    def rehacer(self, event=None):
        if self.indice_historial >= len(self.historial_archivos) - 1:
            self._escribir_consola("No hay más acciones para rehacer.\n")
            return "break"
        self.indice_historial += 1
        self._cargar_snapshot(self.indice_historial)
        return "break"

    def _cargar_snapshot(self, indice):
        ruta = self.historial_archivos[indice]
        with open(ruta, "r", encoding="utf-8") as f:
            contenido = f.read()
        self._restaurando = True
        posicion_cursor = self.texto.index("insert")
        self.texto.delete("1.0", "end")
        self.texto.insert("1.0", contenido)
        try:
            self.texto.mark_set("insert", posicion_cursor)
        except tk.TclError:
            pass
        self._restaurando = False

    def _limpiar_historial_temporal(self):
        shutil.rmtree(self.dir_temporal, ignore_errors=True)

    # Buscar y Reemplazar (se excluyen los operadores aritmeticos
    OPERADORES_PROHIBIDOS = "+-*/="

    @staticmethod
    def _es_caracter_palabra(ch):
        return bool(ch) and (ch.isalnum() or ch == "_")

    @classmethod
    def _es_termino_alfanumerico(cls, termino):
        return bool(re.fullmatch(r"\w+", termino))

    @classmethod
    def _validar_termino_busqueda(cls, termino):
        if not termino:
            return False, "Escriba algo para buscar."
        if any(ch in cls.OPERADORES_PROHIBIDOS for ch in termino):
            return False, "Los operadores aritméticos + - * / = no están permitidos en la búsqueda."
        return True, ""

    @classmethod
    def _validar_tecla_entrada(cls, texto_insertado):
        if texto_insertado == "":
            return True  # permite borrar (Backspace/Delete/cortar selección)
        return not any(ch in cls.OPERADORES_PROHIBIDOS for ch in texto_insertado)

    def abrir_buscar_reemplazar(self):
        if self._ventana_buscar is not None and self._ventana_buscar.winfo_exists():
            self._ventana_buscar.lift()
            self._entrada_buscar.focus_set()
            return

        ventana = tk.Toplevel(self.root)
        ventana.title("Buscar y Reemplazar")
        ventana.configure(bg=COLOR_FONDO_MENU)
        ventana.resizable(False, False)
        ventana.transient(self.root)
        self._ventana_buscar = ventana

        tk.Label(ventana, text="Buscar (palabra):", bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO)\
            .grid(row=0, column=0, sticky="e", padx=6, pady=(8, 4))
        self._entrada_buscar = tk.Entry(ventana, width=32, bg=COLOR_FONDO_EDITOR, fg=COLOR_TEXTO,
                                         insertbackground=COLOR_TEXTO)
        self._entrada_buscar.grid(row=0, column=1, columnspan=2, padx=6, pady=(8, 4), sticky="we")

        tk.Label(ventana, text="Reemplazar con:", bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO)\
            .grid(row=1, column=0, sticky="e", padx=6, pady=4)
        self._entrada_reemplazo = tk.Entry(ventana, width=32, bg=COLOR_FONDO_EDITOR, fg=COLOR_TEXTO,
                                            insertbackground=COLOR_TEXTO)
        self._entrada_reemplazo.grid(row=1, column=1, columnspan=2, padx=6, pady=4, sticky="we")

        # Bloquea a nivel de tecla cualquier caracter que no sea de "palabra"
        # (letra/número/guion bajo): asÃ­ +, -, *, /, = nunca llegan a
        # escribirse en los campos de Buscar/Reemplazar.
        vcmd = (ventana.register(self._validar_tecla_entrada), "%S")
        self._entrada_buscar.config(validate="key", validatecommand=vcmd)
        self._entrada_reemplazo.config(validate="key", validatecommand=vcmd)

        self._var_distinguir_mayusculas = tk.BooleanVar(value=False)
        tk.Checkbutton(ventana, text="Distinguir mayÃºsculas/minÃºsculas",
                        variable=self._var_distinguir_mayusculas, bg=COLOR_FONDO_MENU, fg=COLOR_TEXTO,
                        selectcolor=COLOR_FONDO_EDITOR, activebackground=COLOR_FONDO_MENU,
                        activeforeground=COLOR_TEXTO)\
            .grid(row=2, column=0, columnspan=3, sticky="w", padx=6)

        tk.Label(ventana, text="Nota: los operadores + - * / = no se pueden buscar,\n"
                               "reemplazar ni escribir aquí. Cualquier otro símbolo\n"
                               "(comillas, # $ % & () ¿? ¡! _ : ; {} [] < >) sí­ se permite.",
                 bg=COLOR_FONDO_MENU, fg="#9fb7dd", justify="left", font=("Consolas", 8))\
            .grid(row=3, column=0, columnspan=3, sticky="w", padx=6, pady=(2, 6))

        marco_botones = tk.Frame(ventana, bg=COLOR_FONDO_MENU)
        marco_botones.grid(row=4, column=0, columnspan=3, pady=(0, 6))
        tk.Button(marco_botones, text="Buscar siguiente", command=self.buscar_siguiente).pack(side="left", padx=4)
        tk.Button(marco_botones, text="Reemplazar", command=self.reemplazar_actual).pack(side="left", padx=4)
        tk.Button(marco_botones, text="Reemplazar todo", command=self.reemplazar_todo).pack(side="left", padx=4)
        tk.Button(marco_botones, text="Cerrar", command=ventana.destroy).pack(side="left", padx=4)

        self._etiqueta_estado_buscar = tk.Label(ventana, text="", bg=COLOR_FONDO_MENU, fg=COLOR_ACENTO,
                                                 anchor="w", justify="left")
        self._etiqueta_estado_buscar.grid(row=5, column=0, columnspan=3, sticky="we", padx=6, pady=(0, 8))

        ventana.bind("<Return>", lambda e: self.buscar_siguiente())
        ventana.protocol("WM_DELETE_WINDOW", self._cerrar_ventana_buscar)
        self._entrada_buscar.focus_set()

    def _cerrar_ventana_buscar(self):
        self.texto.tag_remove("resaltado_busqueda", "1.0", "end")
        self._ventana_buscar.destroy()

    def buscar_siguiente(self, desde_inicio=False):
        termino = self._entrada_buscar.get()
        valido, mensaje = self._validar_termino_busqueda(termino)
        self.texto.tag_remove("resaltado_busqueda", "1.0", "end")
        if not valido:
            self._etiqueta_estado_buscar.config(text=mensaje)
            return None

        distinguir = self._var_distinguir_mayusculas.get()
        inicio = "1.0" if desde_inicio else self.texto.index("insert")
        idx = self.texto.search(termino, inicio, stopindex="end", nocase=not distinguir)

        exigir_palabra_completa = self._es_termino_alfanumerico(termino)
        while idx:
            fin = f"{idx}+{len(termino)}c"
            if exigir_palabra_completa:
                caracter_antes = self.texto.get(f"{idx}-1c", idx)
                caracter_despues = self.texto.get(fin, f"{fin}+1c")
                coincide = (not self._es_caracter_palabra(caracter_antes)
                            and not self._es_caracter_palabra(caracter_despues))
            else:
                coincide = True
            if coincide:
                self.texto.tag_add("resaltado_busqueda", idx, fin)
                self.texto.tag_config("resaltado_busqueda", background=COLOR_ACENTO, foreground="white")
                self.texto.mark_set("insert", fin)
                self.texto.see(idx)
                self._etiqueta_estado_buscar.config(text=f"Coincidencia encontrada en la posiciÃ³n {idx}.")
                return idx
            idx = self.texto.search(termino, fin, stopindex="end", nocase=not distinguir)

        if not desde_inicio:
            self._etiqueta_estado_buscar.config(text="Se llegará al final del código, buscando desde el inicio...")
            return self.buscar_siguiente(desde_inicio=True)

        self._etiqueta_estado_buscar.config(text="No se encontraron coincidencias.")
        return None

    def reemplazar_actual(self):
        termino = self._entrada_buscar.get()
        reemplazo = self._entrada_reemplazo.get()
        valido, mensaje = self._validar_termino_busqueda(termino)
        if not valido:
            self._etiqueta_estado_buscar.config(text=mensaje)
            return

        rangos = self.texto.tag_ranges("resaltado_busqueda")
        if not rangos:
            if self.buscar_siguiente() is None:
                return
            rangos = self.texto.tag_ranges("resaltado_busqueda")
            if not rangos:
                return

        inicio, fin = rangos[0], rangos[1]
        self._guardar_snapshot()  # captura el estado ANTES del reemplazo
        self.texto.delete(inicio, fin)
        self.texto.insert(inicio, reemplazo)
        self.texto.mark_set("insert", f"{inicio}+{len(reemplazo)}c")
        self._guardar_snapshot(forzar=True)  # y el estado DESPUÉS, para poder deshacer/rehacer
        self._etiqueta_estado_buscar.config(text="Reemplazado. Buscando la siguiente coincidencia...")
        self.buscar_siguiente()

    def reemplazar_todo(self):
        termino = self._entrada_buscar.get()
        reemplazo = self._entrada_reemplazo.get()
        valido, mensaje = self._validar_termino_busqueda(termino)
        if not valido:
            self._etiqueta_estado_buscar.config(text=mensaje)
            return

        distinguir = self._var_distinguir_mayusculas.get()
        flags = 0 if distinguir else re.IGNORECASE
        # Si el término es un identificador (palabra reservada o variable) (;, {, ", etc.) se busca tal cual, de forma literal.
        if self._es_termino_alfanumerico(termino):
            patron = re.compile(r"\b" + re.escape(termino) + r"\b", flags)
        else:
            patron = re.compile(re.escape(termino), flags)

        contenido = self._obtener_codigo()
        nuevo_contenido, num_reemplazos = patron.subn(reemplazo, contenido)

        if num_reemplazos == 0:
            self._etiqueta_estado_buscar.config(text="No se encontraron coincidencias para reemplazar.")
            return

        self.texto.tag_remove("resaltado_busqueda", "1.0", "end")
        self._guardar_snapshot()  # captura el estado ANTES del reemplazo masivo
        self.texto.delete("1.0", "end")
        self.texto.insert("1.0", nuevo_contenido)
        self._guardar_snapshot(forzar=True)  # y el estado DESPUÉS
        self._etiqueta_estado_buscar.config(text=f"Se reemplazaron {num_reemplazos} coincidencia(s).")
        self._escribir_consola(
            f"Buscar y Reemplazar: '{termino}' -> '{reemplazo}' ({num_reemplazos} reemplazo(s)).\n"
        )

    def _resaltar_lineas_error(self, mensajes):
        """Marca en rojo unicamente las líneas del editor asociadas a errores."""
        if not hasattr(self, "texto"):
            return
        self.texto.tag_remove("linea_error", "1.0", "end")
        lineas = set()
        for mensaje in mensajes:
            for coincidencia in re.finditer(r"(?:ERROR\s+EN\s+L[í]NEA|L[í]NEA)\s+(\d+)",
                                            str(mensaje), re.IGNORECASE):
                lineas.add(int(coincidencia.group(1)))
        total = int(self.texto.index("end-1c").split(".")[0])
        for numero in sorted(lineas):
            if 1 <= numero <= total:
                self.texto.tag_add("linea_error", f"{numero}.0", f"{numero}.end")

    def _escribir_consola(self, mensaje, limpiar=False):
        # Cualquier análisis que envíe diagnósticos a la consola también marca
        # las líneas correspondientes en el editor; los mensajes normales no se colorean.
        if hasattr(self, "texto"):
            self._resaltar_lineas_error(str(mensaje).splitlines())
        if self._esperando_entrada:      # otra acción interrumpió un ACCEPT pendiente
            self._cancelar_ejecucion()
        self.consola.config(state="normal")
        if limpiar:
            self.consola.delete("1.0", "end")
        # Colorea únicamente las líneas de diagnóstico de error; el resto
        # conserva el color normal de la consola.
        for linea in mensaje.splitlines(keepends=True):
            inicio = self.consola.index("end-1c")
            self.consola.insert("end", linea)
            if (re.search(
                    r"\b(ERROR|FALTA|FALTAN|SE ESPERABA|SIN UN|NO ESTÁ]|NO EXISTE|"
                    r"NO SE PUEDE|NO ES VÁLIDO]|NO VÁLIDO|INCOMPLETA|DUPLICADO]|"
                    r"NO RECONOCID[OA]|CADENA SIN CERRAR)\b",
                    linea, re.IGNORECASE)
                    or "[ERROR" in linea.upper()):
                fin = self.consola.index("end-1c")
                self.consola.tag_add("error", inicio, fin)
        self.consola.see("end")
        self.consola.config(state="disabled")

    # Menú Archivo
    def abrir_archivo(self):
        ruta = filedialog.askopenfilename(
            filetypes=[("Archivos de código", "*.c *.txt *.py *.cbl"), ("Todos los archivos", "*.*")]
        )
        if not ruta:
            return
        with open(ruta, "r", encoding="utf-8") as f:
            contenido = f.read()
        self.texto.delete("1.0", "end")
        self.texto.insert("1.0", contenido)
        RUTA_ARCHIVO_ACTUAL["path"] = ruta
        self._escribir_consola(f"Archivo abierto: {ruta}\n")
        self._guardar_snapshot(forzar=True)

    def guardar_archivo(self):
        ruta = RUTA_ARCHIVO_ACTUAL["path"]
        if not ruta:
            ruta = filedialog.asksaveasfilename(
                defaultextension=".c",
                filetypes=[("Archivo C", "*.c"), ("Texto", "*.txt"), ("Todos", "*.*")]
            )
            if not ruta:
                return
            RUTA_ARCHIVO_ACTUAL["path"] = ruta
        with open(ruta, "w", encoding="utf-8") as f:
            f.write(self.texto.get("1.0", "end-1c"))
        self._escribir_consola(f"Archivo guardado en: {ruta}\n")

    def guardar_como(self):
        """Guarda el código en una nueva ubicación y actualiza el archivo actual."""
        ruta = filedialog.asksaveasfilename(
            title="Guardar como",
            defaultextension=".cbl",
            filetypes=[
                ("Archivo COBOL", "*.cbl"),
                ("Archivo COBOL", "*.cob"),
                ("Texto", "*.txt"),
                ("Todos los archivos", "*.*")
            ]
        )
        if not ruta:
            return

        with open(ruta, "w", encoding="utf-8") as f:
            f.write(self.texto.get("1.0", "end-1c"))

        RUTA_ARCHIVO_ACTUAL["path"] = ruta
        self._escribir_consola(f"Archivo guardado como: {ruta}\n")

    def limpiar_pantalla(self):
        self.texto.delete("1.0", "end")
        self._escribir_consola("", limpiar=True)
        self._escribir_consola("Pantalla limpiada.\n")
        self._guardar_snapshot(forzar=True)

    def cerrar_app(self):
        if messagebox.askyesno("Cerrar", "¿Desea cerrar el compilador?"):
            self._limpiar_historial_temporal()
            self.root.destroy()

    # Menú Ayuda -> Divisiones (COBOL) / Estructura del código
    def insertar_division(self, nombre_division):
    
        linea = f"{nombre_division}.\n"
        contenido_actual = self.texto.get("1.0", "end-1c")
        if linea.strip() in contenido_actual:
            self._escribir_consola(f"La {nombre_division} ya estaba agregada.\n")
            return

        indice_nueva = ORDEN_DIVISIONES_COBOL.index(nombre_division)
        posicion_insercion = "end"
      
        for division_posterior in ORDEN_DIVISIONES_COBOL[indice_nueva + 1:]:
            pos = self.texto.search(f"{division_posterior}.", "1.0", stopindex="end")
            if pos:
                posicion_insercion = pos
                break

        self.texto.insert(posicion_insercion, linea)
        self._escribir_consola(f"{nombre_division} agregada.\n")
        self._guardar_snapshot(forzar=True)

    def insertar_estructura_cobol(self):
      
        contenido_actual = self.texto.get("1.0", "end-1c")
        if "PROGRAM-ID." in contenido_actual:
            if not messagebox.askyesno(
                "Estructura del código",
                "Ya hay una estructura COBOL en el editor. ¿Agregar otra copia de todas formas?"
            ):
                return
        separador = "\n" if contenido_actual.strip() else ""
        self.texto.insert("end", separador + ESTRUCTURA_COBOL)
        self._escribir_consola("Estructura del código (COBOL) agregada.\n")
        self._guardar_snapshot(forzar=True)

    # Menú Variables -> Tipos
    def insertar_variable(self, tipo):
        
        pic = TIPO_PIC_COBOL.get(tipo, "PIC X(20)")
        contador = self._contadores_variables.setdefault(tipo, 0) + 1
        self._contadores_variables[tipo] = contador
        nombre_var = f"VARIABLE-{tipo.upper()}-{contador}"
        declaracion = f"           01 {nombre_var} {pic}.\n"

        posicion_insercion = self._buscar_posicion_working_storage()
        self.texto.insert(posicion_insercion, declaracion)
        if posicion_insercion == "end":
            self._escribir_consola(
                "Aviso: no se encontró WORKING-STORAGE SECTION, la variable se "
                "agregó al final. Use Ayuda > Estructura del código o Ayuda > "
                "Divisiones > DATA DIVISION primero.\n"
            )
        self._escribir_consola(f"Variable insertada: {declaracion.strip()}\n")
        self._guardar_snapshot(forzar=True)

    def _buscar_posicion_working_storage(self):
      
        pos_ws = self.texto.search("WORKING-STORAGE SECTION.", "1.0", stopindex="end")
        if pos_ws:
            fin_linea = self.texto.index(f"{pos_ws} lineend +1c")
            return fin_linea
        pos_proc = self.texto.search("PROCEDURE DIVISION.", "1.0", stopindex="end")
        if pos_proc:
            return pos_proc
        return "end"

    # Menú Compiladores: fases del compilador
    def _obtener_codigo(self):
        return self.texto.get("1.0", "end-1c")

    # Palabras reservadas de COBOL que reconoce el analizador léxico
    PALABRAS_RESERVADAS_COBOL = {
        "ACCEPT", "ADD", "ALTER", "CALL", "CLOSE", "COMPUTE",
        "CONFIGURATION", "CONTINUE", "DATA", "DELETE", "DISPLAY",
        "DIVIDE", "DIVISION", "ELSE", "END", "END-IF", "END-PERFORM",
        "END-READ", "END-WRITE", "ENVIRONMENT", "EVALUATE", "EXIT",
        "FILE", "FROM", "GIVING", "GO", "IF", "IDENTIFICATION",
        "INITIALIZE", "INPUT-OUTPUT", "INSPECT", "MOVE", "MULTIPLY",
        "OPEN", "PERFORM", "PIC", "PICTURE", "PROGRAM", "PROGRAM-ID",
        "PROCEDURE", "READ", "REDEFINES", "REWRITE", "RUN", "SEARCH",
        "SECTION", "SET", "START", "STOP", "STRING", "SUBTRACT",
        "TO", "UNSTRING", "UNTIL", "VALUE", "VARYING", "WHEN",
        "WORKING-STORAGE", "WRITE", "AUTHOR", "END PROGRAM",
        # usadas en la condicion del IF
        "THEN", "AND", "OR", "NOT", "IS", "EQUAL", "GREATER", "LESS",
        "THAN", "NUMERIC", "ALPHABETIC",
        # usadas en EVALUATE (switch)
        "OTHER", "END-EVALUATE", "ALSO", "THRU", "THROUGH", "TRUE", "FALSE", "ANY",
        # usadas en PERFORM VARYING (for) y aritmética
        "BY", "TIMES", "INTO", "ROUNDED", "REMAINDER",
    }

    @staticmethod
    def _quitar_comentarios_cobol(codigo):
      
        lineas = []
        for linea in codigo.splitlines():
            if linea.strip().startswith("*"):
                lineas.append("")
            else:
                lineas.append(linea)
        return "\n".join(lineas)

    def alternar_palabras_reservadas(self):
        #Activa o desactiva el resaltado visual de palabras reservadas.
        if self.palabras_reservadas_activas.get():
            self.resaltar_palabras_reservadas()
        else:
            self.texto.tag_remove("palabra_reservada", "1.0", "end")

    def resaltar_palabras_reservadas(self):
      # Busca las palabras reservadas de COBOL y las pinta de azul y negrita.
        self.texto.tag_remove("palabra_reservada", "1.0", "end")
        self.texto.tag_config(
            "palabra_reservada",
            foreground="blue",
            font=("Courier", 10, "bold")
        )

        codigo = self._obtener_codigo()
        if not codigo:
            return

        for palabra in self.PALABRAS_RESERVADAS_COBOL:
            patron = re.compile(
                r"(?<![A-Za-z0-9-])" + re.escape(palabra) +
                r"(?![A-Za-z0-9-])",
                re.IGNORECASE
            )

            for match in patron.finditer(codigo):
                inicio_index = f"1.0 + {match.start()} chars"
                fin_index = f"1.0 + {match.end()} chars"
                self.texto.tag_add(
                    "palabra_reservada",
                    inicio_index,
                    fin_index
                )

    def analisis_lexico(self, mostrar=True):
        codigo = self._quitar_comentarios_cobol(self._obtener_codigo())
        self._errores_lexicos = []
        if not codigo.strip():
            if mostrar:
                self._escribir_consola("No hay código para analizar.\n")
            return []
        self.resaltar_palabras_reservadas()
        patron = re.compile(r"""
            (?P<CADENA>"[^"\n]*"|'[^'\n]*')
          | (?P<NUMERO>\d+\.\d+|\d+)
          | (?P<IDENTIFICADOR>[A-Za-z][A-Za-z0-9-]*)
          | (?P<OPERADOR>>=|<=|<>|\*\*|[=<>+\-*/])
          | (?P<PARENTESIS>[()])
          | (?P<PERIODO>\.)
        """, re.VERBOSE)
        tokens, posicion = [], 0
        for m in patron.finditer(codigo):
            tramo = codigo[posicion:m.start()]
            for k, ch in enumerate(tramo):
                if not ch.isspace():
                    absoluto = posicion + k
                    linea = codigo.count("\n", 0, absoluto) + 1
                    col = absoluto - codigo.rfind("\n", 0, absoluto)
                    self._errores_lexicos.append(
                        f"ERROR EN LÍNEA {linea}, COLUMNA {col}: carácter no reconocido '{ch}'.")
            tipo, valor = m.lastgroup, m.group()
            if tipo == "IDENTIFICADOR" and valor.upper() in self.PALABRAS_RESERVADAS_COBOL:
                tipo = "PALABRA_RESERVADA"
            linea = codigo.count("\n", 0, m.start()) + 1
            col = m.start() - codigo.rfind("\n", 0, m.start())
            tokens.append((valor, tipo, linea, col))
            posicion = m.end()
        for k, ch in enumerate(codigo[posicion:]):
            if not ch.isspace():
                absoluto = posicion + k
                linea = codigo.count("\n", 0, absoluto) + 1
                col = absoluto - codigo.rfind("\n", 0, absoluto)
                self._errores_lexicos.append(
                    f"ERROR EN LÍNEA {linea}, COLUMNA {col}: carácter no reconocido '{ch}'.")
        for num, linea_txt in enumerate(codigo.splitlines(), 1):
            if linea_txt.count('"') % 2 or linea_txt.count("'") % 2:
                self._errores_lexicos.append(
                    f"ERROR EN LÍNEA {num}: cadena sin cerrar; falta la comilla correspondiente.")
        if mostrar:
            salida = ["=== ANÁLISIS LÉXICO (COBOL) ==="]
            salida.extend(f"Token({tipo}, '{valor}', L:{linea}, C:{col})"
                          for valor, tipo, linea, col in tokens)
            if self._errores_lexicos:
                salida.append("Errores léxicos:")
                salida.extend(self._errores_lexicos)
            salida.append(f"Token(EOF, 'EOF', L:{len(codigo.splitlines()) + 1}, C:1)")
            salida.append(f"Total de tokens: {len(tokens)}\n")
            self._escribir_consola("\n".join(salida) + "\n")
        return tokens

    def _validar_estructura_global(self, codigo):
        errores = []
        lineas = codigo.splitlines()
        obligatorias = ["IDENTIFICATION DIVISION", "DATA DIVISION", "PROCEDURE DIVISION"]
        orden = ["IDENTIFICATION DIVISION", "ENVIRONMENT DIVISION",
                 "DATA DIVISION", "PROCEDURE DIVISION"]
        posiciones = {}
        for encabezado in orden:
            m = re.search(r"(?im)^\s*" + re.escape(encabezado) + r"\b", codigo)
            posiciones[encabezado] = m.start() if m else -1
            if encabezado in obligatorias and not m:
                errores.append(f"ERROR EN LÍNEA 1: falta '{encabezado}.' (división obligatoria).")
        presentes = [x for x in orden if posiciones[x] >= 0]
        if presentes != sorted(presentes, key=lambda x: posiciones[x]):
            errores.append("ERROR EN LÍNEA 1: las divisiones están fuera de orden.")
        for encabezado in orden + ["FILE SECTION", "WORKING-STORAGE SECTION"]:
            for num, linea in enumerate(lineas, 1):
                if re.search(re.escape(encabezado) + r"\b", linea, re.IGNORECASE):
                    if not re.match(r"\s*" + re.escape(encabezado) + r"\s*\.", linea, re.IGNORECASE):
                        errores.append(f"ERROR EN LÍNEA {num}: falta el punto (.) después de '{encabezado}'.")
        m_id = re.search(r"(?im)^\s*PROGRAM-ID\s*\.\s*([A-Za-z][A-Za-z0-9-]*)\s*\.", codigo)
        m_end = re.search(r"(?im)^\s*END\s+PROGRAM\s+([A-Za-z][A-Za-z0-9-]*)\s*\.", codigo)
        if not m_id:
            num = next((i for i, x in enumerate(lineas, 1) if "PROGRAM-ID" in x.upper()), 1)
            errores.append(f"ERROR EN LÍNEA {num}: falta 'PROGRAM-ID. nombre.'.")
        if not m_end:
            errores.append(f"ERROR EN LÍNEA {max(1, len(lineas))}: falta 'END PROGRAM nombre.'.")
        if m_id and m_end and m_id.group(1).upper() != m_end.group(1).upper():
            num = codigo.count("\n", 0, m_end.start()) + 1
            errores.append(f"ERROR EN LÍNEA {num}: END PROGRAM no coincide con PROGRAM-ID.")
        if not re.search(r"(?i)\bSTOP\s+RUN\s*\.", codigo):
            errores.append(f"ERROR EN LÍNEA {max(1, len(lineas))}: falta 'STOP RUN.'.")
        dentro_ws = False
        declaradas = {}
        for num, linea in enumerate(lineas, 1):
            upper = linea.upper()
            if "WORKING-STORAGE SECTION." in upper:
                dentro_ws = True
                continue
            if "PROCEDURE DIVISION." in upper:
                dentro_ws = False
            if dentro_ws and re.match(r"\s*\d+\s+", linea):
                m = re.match(r"\s*(\d+)\s+([A-Za-z][A-Za-z0-9-]*)\s+PIC(?:TURE)?\s+(.+?)\s*\.\s*$",
                             linea, re.IGNORECASE)
                if not m:
                    errores.append(f"ERROR EN LÍNEA {num}: declaración incompleta; falta nombre, PIC o punto final.")
                    continue
                _, nombre, pic = m.groups()
                if nombre.upper() in declaradas:
                    errores.append(f"ERROR EN LÍNEA {num}: variable '{nombre}' duplicada; ya existe en línea {declaradas[nombre.upper()]}.")
                else:
                    declaradas[nombre.upper()] = num
                if not re.fullmatch(r"S?9(?:\(\d+\))?(?:V9(?:\(\d+\))?)?|X(?:\(\d+\))?|A(?:\(\d+\))?",
                                    pic.strip(), re.IGNORECASE):
                    errores.append(f"ERROR EN LÍNEA {num}: tipo PIC no válido: '{pic.strip()}'.")
        return errores

    def analisis_sintactico(self):
        codigo_original = self._obtener_codigo()
        if not codigo_original.strip():
            self._escribir_consola("No hay código para analizar.\n")
            return False
        codigo = self._quitar_comentarios_cobol(codigo_original)
        errores = self._validar_estructura_global(codigo)
        tokens = self.analisis_lexico(mostrar=False)
        errores.extend(getattr(self, "_errores_lexicos", []))
        tabla = self._obtener_tabla_simbolos(codigo)
        sintactico = AnalizadorSintactico(tokens, exigir_end_if=False, tabla_simbolos=tabla)
        sintactico.analizar()
        errores.extend(sintactico.errores)
        errores.extend(sintactico.errores_semanticos)

        # Detectar nombres usados en PROCEDURE que no existen en WORKING-STORAGE.
        m_proc = re.search(r"PROCEDURE DIVISION\.(.*?)(?:END\s+PROGRAM\b|\Z)",
                           codigo, re.IGNORECASE | re.DOTALL)
        if m_proc:
            cuerpo = m_proc.group(1)
            cuerpo_limpio = re.sub(r"""("[^"]*"|'[^']*')""", "", cuerpo)
            parrafos = {x.upper() for x in re.findall(
                r"(?im)^\s*([A-Za-z][A-Za-z0-9-]*)\.\s*$", cuerpo)}
            vistos = set()
            for m in re.finditer(r"\b[A-Za-z][A-Za-z0-9-]*\b", cuerpo_limpio):
                nombre = m.group()
                upper = nombre.upper()
                if (upper in tabla or upper in parrafos
                        or upper in self.PALABRAS_RESERVADAS_COBOL
                        or upper in {"ZERO", "ZEROS", "SPACE", "SPACES", "TRUE", "FALSE"}):
                    continue
                if upper not in vistos:
                    vistos.add(upper)
                    linea = codigo.count("\n", 0, m_proc.start()) + cuerpo.count("\n", 0, m.start()) + 1
                    errores.append(
                        f"ERROR EN LÍNEA {linea}: la variable '{nombre}' no está declarada "
                        "en WORKING-STORAGE SECTION."
                    )

        # Comprobación básica de compatibilidad de tipos en MOVE y operaciones aritméticas.
        tipos = {nombre.upper(): AnalizadorSintactico._tipo_desde_pic(pic) for nombre, pic in tabla.items()}
        for num, linea_txt in enumerate(codigo.splitlines(), 1):
            move = re.search(r"(?i)\bMOVE\s+(\"[^\"]*\"|'[^']*'|[-+]?\d+(?:\.\d+)?|[A-Za-z][A-Za-z0-9-]*)\s+TO\s+([A-Za-z][A-Za-z0-9-]*)", linea_txt)
            if move:
                origen, destino = move.groups()
                tipo_origen = ("alfanumerico" if origen.startswith(('"', "'")) else
                               "numerico" if re.fullmatch(r"[-+]?\\d+(?:\\.\\d+)?", origen) else
                               tipos.get(origen.upper()))
                tipo_destino = tipos.get(destino.upper())
                if tipo_origen and tipo_destino and tipo_origen != tipo_destino:
                    errores.append(
                        f"ERROR EN LÍNEA {num}: no se puede mover un valor {tipo_origen} "
                        f"a '{destino}', que es {tipo_destino}."
                    )
            if re.search(r"(?i)\b(?:ADD|SUBTRACT|MULTIPLY|DIVIDE)\s+(\"[^\"]*\"|'[^']*')", linea_txt):
                errores.append(
                    f"ERROR EN LÍNEA {num}: una operación aritmética no puede utilizar cadenas de texto."
                )

        salida = ["=== ANÁLISIS SINTÁCTICO Y SEMÁNTICO (COBOL) ==="]
        if errores:
            salida.append("COMPILACIÓN BLOQUEADA. Corrija los siguientes errores:")
            salida.extend(errores)
        else:
            salida.append("Estructura, sintaxis y reglas semánticas correctas.")
        if sintactico.advertencias:
            salida.append("Advertencias:")
            salida.extend(sintactico.advertencias)
        self._resaltar_lineas_error(errores)
        self._escribir_consola("\n".join(salida) + "\n\n")
        return not errores

    def analisis_condicional_if(self):
        """Compiladores > Sintactico: Condicional IF (solo verifica los IF)."""
        if not self._obtener_codigo().strip():
            self._escribir_consola("No hay código para analizar.\n")
            return False
        tokens = self.analisis_lexico(mostrar=False)
        total_if = sum(1 for t in tokens if t[1] != "CADENA" and t[0].upper() == "IF")
        sintactico = AnalizadorSintactico(tokens)
        correcto = sintactico.analizar()

        salida = ["=== Analisis Sintactico: Condicional IF (COBOL) ==="]
        salida.append(f"Sentencias IF encontradas: {total_if}")
        if correcto and total_if == 0:
            salida.append("No se encontró ningún IF en el código.")
        elif correcto:
            salida.append("Sintaxis correcta: todos los IF están bien formados.")
        else:
            salida.append("Se encontraron errores:")
            salida.extend(sintactico.errores)
        if sintactico.advertencias:
            salida.append("Advertencias:")
            salida.extend(sintactico.advertencias)
        self._escribir_consola("\n".join(salida) + "\n\n")
        return correcto

    def _obtener_tabla_simbolos(self, codigo):
        """{NOMBRE: PIC} de las variables de WORKING-STORAGE (sin imprimir nada)."""
        declaraciones = re.findall(
            r"^\s*\d+\s+([A-Za-z][A-Za-z0-9-]*)\s+PIC(?:TURE)?\s+([^\.\n]+?)"
            r"(?:\s+VALUE\s+(\"[^\"]*\"|'[^']*'|[-+]?\d+(?:\.\d+)?))?\s*\.",
            codigo, re.IGNORECASE | re.MULTILINE)
        tabla = TablaSimbolos()
        for nombre, pic, valor in declaraciones:
            tabla[nombre.upper()] = pic.strip()
            if valor:
                tabla.valores[nombre.upper()] = (
                    valor[1:-1] if valor[0] in "\"'" else
                    (float(valor) if "." in valor else int(valor)))
        return tabla

    def analisis_condicional_switch(self):
        """Compiladores > Condicional Switch (EVALUATE):
        léxico + reglas sintácticas + reglas semánticas."""
        codigo = self._obtener_codigo()
        if not codigo.strip():
            self._escribir_consola("No hay código para analizar.\n")
            return False

        tokens = self.analisis_lexico(mostrar=True)          # análisis léxico (módulo anterior)
        tabla = self._obtener_tabla_simbolos(self._quitar_comentarios_cobol(codigo))
        analizador = AnalizadorSintactico(tokens, tabla_simbolos=tabla)
        analizador.analizar()
        total = sum(1 for t in tokens if t[1] != "CADENA" and t[0].upper() == "EVALUATE")

        salida = ["=== Analisis Condicional Switch: EVALUATE (COBOL) ===",
                  f"Estructuras EVALUATE encontradas: {total}"]
        if total == 0:
            salida.append("No se encontró ningún EVALUATE en el código.")
        salida.append("Reglas sintácticas:")
        if analizador.errores:
            salida.extend(analizador.errores)
        else:
            salida.append("  Correctas.")
        salida.append("Reglas semánticas:")
        if analizador.errores_semanticos:
            salida.extend(analizador.errores_semanticos)
        else:
            salida.append("  Correctas.")
        if analizador.advertencias:
            salida.append("Advertencias:")
            salida.extend(analizador.advertencias)
        self._escribir_consola("\n".join(salida) + "\n\n")
        return not analizador.errores and not analizador.errores_semanticos

    def analisis_iteracion_for(self):
        """Compiladores > For (PERFORM VARYING):
        léxico + reglas sintácticas + reglas semánticas de la iteración."""
        codigo = self._obtener_codigo()
        if not codigo.strip():
            self._escribir_consola("No hay código para analizar.\n")
            return False

        tokens = self.analisis_lexico(mostrar=True)      
        tabla = self._obtener_tabla_simbolos(self._quitar_comentarios_cobol(codigo))
        analizador = AnalizadorSintactico(tokens, tabla_simbolos=tabla)
        analizador.analizar()
        total = sum(1 for t in tokens if t[1] != "CADENA" and t[0].upper() == "VARYING")

        salida = ["=== Analisis Iteracion FOR: PERFORM VARYING (COBOL) ===",
                  f"Ciclos PERFORM VARYING encontrados: {total}"]
        if total == 0:
            salida.append("No se encontró ningún PERFORM VARYING en el código.")
        salida.append("Reglas sintácticas:")
        if analizador.errores:
            salida.extend(analizador.errores)
        else:
            salida.append("  Correctas.")
        salida.append("Reglas semánticas:")
        if analizador.errores_semanticos:
            salida.extend(analizador.errores_semanticos)
        else:
            salida.append("  Correctas.")
        if analizador.advertencias:
            salida.append("Advertencias:")
            salida.extend(analizador.advertencias)
        self._escribir_consola("\n".join(salida) + "\n\n")
        return not analizador.errores and not analizador.errores_semanticos

    def analisis_estructuras_anidadas(self):
        """Compiladores > Estructuras anidadas (while + if):
        léxico + mapa de anidamiento + reglas sintácticas y semánticas."""
        codigo = self._obtener_codigo()
        if not codigo.strip():
            self._escribir_consola("No hay código para analizar.\n")
            return False

        tokens = self.analisis_lexico(mostrar=True)         
        tabla = self._obtener_tabla_simbolos(self._quitar_comentarios_cobol(codigo))
        analizador = AnalizadorSintactico(tokens, tabla_simbolos=tabla)
        analizador.analizar()

        salida = ["=== Analisis Estructuras Anidadas (COBOL) ===",
                  f"Estructuras encontradas: {len(analizador.estructuras)}   "
                  f"Nivel máximo de anidamiento: {analizador.max_nivel}"]
        if analizador.estructuras:
            salida.append("Mapa de anidamiento:")
            for nivel, etiqueta, linea in analizador.estructuras:
                salida.append(f"  {'    ' * (nivel - 1)}{etiqueta} (lí­nea {linea})")
        else:
            salida.append("No se encontrarón ninguna estructura IF, EVALUATE o PERFORM.")
        salida.append("Reglas sintácticas:")
        if analizador.errores:
            salida.extend(analizador.errores)
        else:
            salida.append("  Correctas.")
        salida.append("Reglas semánticas:")
        if analizador.errores_semanticos:
            salida.extend(analizador.errores_semanticos)
        else:
            salida.append("  Correctas.")
        if analizador.advertencias:
            salida.append("Advertencias:")
            salida.extend(analizador.advertencias)
        self._escribir_consola("\n".join(salida) + "\n\n")
        return not analizador.errores and not analizador.errores_semanticos

    def analisis_semantico(self):
        codigo_original = self._obtener_codigo()
        if not codigo_original.strip():
            self._escribir_consola("No hay código para analizar.\n")
            return

        codigo = self._quitar_comentarios_cobol(codigo_original)
        salida = ["=== Analisis Semantico (COBOL) === "]

        declaraciones = re.findall(
            r"^\s*\d+\s+([A-Za-z][A-Za-z0-9-]*)\s+PIC(?:TURE)?\s+([^\.\n]+?)"
            r"(?:\s+VALUE\s+(\"[^\"]*\"|'[^']*'|[-+]?\d+(?:\.\d+)?))?\s*\.",
            codigo, re.IGNORECASE | re.MULTILINE
        )
        tabla_simbolos = {}
        for nombre, pic, valor in declaraciones:
            tabla_simbolos[nombre.upper()] = pic.strip()
            detalle_valor = f", valor inicial {valor}" if valor else ""
            salida.append(f"  Variable '{nombre}' declarada con PIC {pic.strip()}{detalle_valor}.")
        if not declaraciones:
            salida.append("  No se encontraron variables declaradas en WORKING-STORAGE SECTION.")

        # El nombre de PROGRAM-ID debe coincidir con el de END PROGRAM
        m_id = re.search(r"PROGRAM-ID\.\s*([A-Za-z0-9-]+)\s*\.", codigo, re.IGNORECASE)
        m_end = re.search(r"END\s+PROGRAM\s+([A-Za-z0-9-]+)\s*\.", codigo, re.IGNORECASE)
        if m_id and m_end:
            if m_id.group(1).upper() != m_end.group(1).upper():
                salida.append(f"  El nombre en PROGRAM-ID ('{m_id.group(1)}') no coincide "
                               f"con END PROGRAM ('{m_end.group(1)}').")
            else:
                salida.append(f"  El nombre del programa coincide en PROGRAM-ID y END PROGRAM "
                               f"('{m_id.group(1)}').")

        m_proc = re.search(r"PROCEDURE DIVISION\.(.*?)(?:END\s+PROGRAM\b|\Z)",
                            codigo, re.IGNORECASE | re.DOTALL)
        cuerpo_proc = m_proc.group(1) if m_proc else ""
        cuerpo_sin_cadenas = re.sub(r'"[^"]*"|\'[^\']*\'', '', cuerpo_proc)
        nombres_parrafo = {n.upper() for n in re.findall(
            r"^\s*([A-Za-z][A-Za-z0-9-]*)\.\s*$", cuerpo_proc, re.MULTILINE)}
        identificadores_usados = set(re.findall(r"\b[A-Za-z][A-Za-z0-9-]*\b", cuerpo_sin_cadenas))
        no_declarados = [
            ident for ident in identificadores_usados
            if ident.upper() not in tabla_simbolos
            and ident.upper() not in nombres_parrafo
            and ident.upper() not in self.PALABRAS_RESERVADAS_COBOL
        ]
        if no_declarados:
            salida.append("Identificadores usados en PROCEDURE DIVISION sin declarar en WORKING-STORAGE:")
            for ident in sorted(no_declarados):
                salida.append(f"  - {ident}")
        else:
            salida.append("Todas las variables usadas en PROCEDURE DIVISION están declaradas.")

        # Reglas semÃ¡nticas de EVALUATE (tipos, valores repetidos, rangos...)
        sem = AnalizadorSintactico(self.analisis_lexico(mostrar=False),
                                   tabla_simbolos=self._obtener_tabla_simbolos(codigo))
        sem.analizar()
        if sem.errores_semanticos:
            salida.append("Errores semánticos (IF / EVALUATE / PERFORM):")
            salida.extend(sem.errores_semanticos)

        self._escribir_consola("\n".join(salida) + "\n\n")
        return tabla_simbolos
    # Ejecución del programa (con entrada por consola para ACCEPT)
    def ejecutar_programa(self, al_terminar=None):
        codigo = self._quitar_comentarios_cobol(self._obtener_codigo())

        variables, pics = {}, {}
        for nombre, pic, valor_inicial in re.findall(
            r"^\s*\d+\s+([A-Za-z][A-Za-z0-9-]*)\s+PIC(?:TURE)?\s+([^\.\n]+?)"
            r"(?:\s+VALUE\s+(\"[^\"]*\"|'[^']*'|[-+]?\d+(?:\.\d+)?))?\s*\.",
            codigo, re.IGNORECASE | re.MULTILINE
        ):
            nombre_u, pic_u = nombre.upper(), pic.strip().upper()
            pics[nombre_u] = pic_u
            if valor_inicial:
                if valor_inicial[0] in "\"'":
                    variables[nombre_u] = valor_inicial[1:-1]
                else:
                    variables[nombre_u] = float(valor_inicial) if "." in valor_inicial else int(valor_inicial)
            elif pic_u.startswith(("9", "S9")):
                variables[nombre_u] = 0
            else:
                variables[nombre_u] = ""

        self._escribir_consola("=== Salida del programa ===\n")
        interprete = InterpreteCOBOL(self.analisis_lexico(mostrar=False), variables, pics,
                                     self._escribir_consola)
        try:
            interprete.preparar()
        except ErrorEjecucion as e:
            self._escribir_consola(f"[Error de ejecución: {e}]\n\n")
            if al_terminar:
                al_terminar()
            return False

        self._interprete = interprete
        self._gen = interprete.ejecutar()
        self._al_terminar = al_terminar
        self._avanzar_ejecucion(None)
        return True

    def _avanzar_ejecucion(self, entrada):
        """Reanuda el programa; se detiene en cada ACCEPT para pedir un valor."""
        gen = self._gen
        if gen is None:
            return
        try:
            variable, pic = gen.send(entrada)
        except StopIteration:
            self._finalizar_ejecucion()
            return
        except ErrorEjecucion as e:
            self._escribir_consola(f"[Error de ejecución: {e}]\n")
            self._finalizar_ejecucion()
            return
        self._pedir_entrada()

    def _pedir_entrada(self):
        c = self.consola
        c.config(state="normal")                 # la consola se vuelve editable
        c.insert("end", "> ")
        c.mark_set("inicio_entrada", "end-1c")   # lo escrito antes de esta marca no se puede borrar
        c.mark_gravity("inicio_entrada", "left")
        c.mark_set("insert", "end-1c")
        c.see("end")
        c.focus_set()
        self._esperando_entrada = True

    def _filtrar_tecla(self, event):
        if not self._esperando_entrada:
            return None
        c = self.consola
        if event.keysym == "BackSpace":
            return "break" if c.compare("insert", "<=", "inicio_entrada") else None
        if event.keysym == "Delete":
            return "break" if c.compare("insert", "<", "inicio_entrada") else None
        if event.keysym in ("Left", "Right", "Up", "Down", "Home", "End", "Shift_L", "Shift_R",
                            "Control_L", "Control_R", "Alt_L", "Alt_R") or event.state & 0x4:
            return None
        if c.compare("insert", "<", "inicio_entrada"):
            c.mark_set("insert", "end-1c")       # solo se escribe al final, junto al ">"
        return None

    def _enviar_entrada(self, event=None):
        if not self._esperando_entrada:
            return "break"
        c = self.consola
        texto = c.get("inicio_entrada", "end-1c").strip()
        self._esperando_entrada = False
        c.insert("end", "\n")
        c.config(state="disabled")
        self._avanzar_ejecucion(texto)
        return "break"

    def _cancelar_ejecucion(self, aviso=True):
        esperaba = self._esperando_entrada
        self._esperando_entrada = False
        gen, self._gen = self._gen, None
        self._al_terminar = None
        if gen is not None:
            gen.close()
        if esperaba:
            self.consola.insert("end", "\n")
            self.consola.config(state="disabled")
            if aviso:
                self._escribir_consola("[Ejecución cancelada: el programa esperaba una entrada.]\n")

    def _finalizar_ejecucion(self):
        interprete = self._interprete
        self._gen = None
        salida = []
        if not interprete.hubo_salida:
            salida.append('(El programa no generó salida. Agregue DISPLAY "..." dentro de PROCEDURE DIVISION.)')
        if not interprete.detenido:
            salida.append("\n[Aviso: no se encontró STOP RUN.; se interpretó todo el cuerpo de todas formas.]")
        if interprete.variables:
            salida.append("\nValores finales de variables:")
            for nombre, valor in interprete.variables.items():
                salida.append(f"  {nombre} = {valor!r}")
        self._escribir_consola("\n".join(salida) + "\n\n")
        terminar, self._al_terminar = self._al_terminar, None
        if terminar:
            terminar()

    def compilar_y_ejecutar(self):
        self._cancelar_ejecucion(aviso=False)
        self._escribir_consola("=== INICIANDO COMPILACIÓN ===\n")
        self.analisis_lexico()
        if not self.analisis_sintactico():
            self._escribir_consola(
                "[COMPILACIÓN CANCELADA] Hay errores léxicos, sintácticos o semánticos. "
                "Corríguelos antes de ejecutar.\n\n")
            return False
        resultado_semantico = self.analisis_semantico()
        if resultado_semantico is False:
            self._escribir_consola(
                "[COMPILACIÓN CANCELADA] La validaciónn semántica no fue satisfactoria.\n\n")
            return False

        def al_terminar():
            self._escribir_consola("Compilación finalizada correctamente.\n\n")

        return self.ejecutar_programa(al_terminar)

def main():
    root = tk.Tk()
    CompiladorApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()