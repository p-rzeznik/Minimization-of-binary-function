"""

Redukcja wyrażenia logicznego
Wszystkie funkcje potrzebne do redukcji wyrażenia logicznego znajdują się w klasie MBF w pliku "MBF.py"

"""

import string
from itertools import combinations
from itertools import compress
import sys


class MBF:
    """ Minimization of binary function"""

    VAR = string.ascii_lowercase
    VAL = "TF"
    OPERATORS = ">&|/^"
    NEGATION = "~"


    def __init__(self, expr):
        self.expr = self.remove_spaces(expr)

        self.correct = True
        if not MBF.check(expr):
            self.correct = False
            return

        self.always_false = False
        if MBF.tautology(MBF.negate(self.expr)):
            self.always_false = True
            return

        self.labels = self.get_labels()
        vec_set = self.expr_to_set()
        self.vec_list = list(MBF.minimum(vec_set, MBF.reduce(vec_set)))

    def get_labels(self):
        return sorted(list((set(self.expr) & set(MBF.VAR))))

    def minimize(self, stdout=True):
        """Funkcja odpowiadająca za minimalizację wyrażenia logicznego i wyświetlenie wyniku minimalizacji"""
        if not self.correct:
            if stdout:
                sys.stdout.write("ERROR")
            else:
                return "ERROR"

        if MBF.tautology(self.expr):
            if stdout:
                sys.stdout.write("T")
            else:
                return "T"

        if self.always_false:
            if stdout:
                sys.stdout.write("F")
            else:
                return "F"

        self.simplify_alternatives()
        self.simplify_xor()
        self.simplify_Shaffter()
        self.simplify_implication()

        result = self.bracket(self.vector_to_func(self.vec_list))

        if len(self.expr) <= len(result):
            result = self.expr

        if stdout:
            sys.stdout.write(result)
        else:
            return result

    @staticmethod
    def remove_spaces(expr):
        return expr.replace(" ", "")

    # ----------------------------------------------------- #
    """Funkcje z ćwiczeń zaadaptowane do potrzeb zadania"""

    @staticmethod
    def check(expr):
        state = True
        bracket_counter = 0
        for c in expr:
            if state:
                if c in ")" + MBF.OPERATORS:
                    return False
                if c in MBF.VAR + MBF.VAL:
                    state = False

            else:
                if c in MBF.VAR + MBF.VAL + "(" + MBF.NEGATION:
                    return False
                if c in MBF.OPERATORS:
                    state = True

            if c == "(":
                bracket_counter += 1
            if c == ")":
                bracket_counter -= 1
                if bracket_counter < 0:
                    return False

        return bracket_counter == 0 and not state

    @staticmethod
    def bracket(expr):
        while expr[0] == "(" and expr[-1] == ")" and MBF.check(expr[1:-1]):
            expr = expr[1:-1]
        return expr

    @staticmethod
    def bal(expr, op):
        bracket_counter = 0
        for i in range(len(expr) - 1, -1, -1):
            if expr[i] == "(":
                bracket_counter -= 1
            if expr[i] == ")":
                bracket_counter += 1
            if expr[i] in op and bracket_counter == 0:
                return i
        return -1

    @staticmethod
    def onp(expr):
        while expr[0] == "(" and expr[-1] == ")" and MBF.check(expr[1:-1]):
            expr = expr[1:-1]

        p = MBF.bal(expr, MBF.OPERATORS[0])
        if p >= 0:
            return MBF.onp(expr[:p]) + MBF.onp(expr[p + 1:]) + expr[p]

        p = MBF.bal(expr, MBF.OPERATORS[1:4])
        if p >= 0:
            return MBF.onp(expr[:p]) + MBF.onp(expr[p + 1:]) + expr[p]

        p = MBF.bal(expr, MBF.OPERATORS[4])
        if p >= 0:
            return MBF.onp(expr[:p]) + MBF.onp(expr[p + 1:]) + expr[p]

        p = MBF.bal(expr, MBF.NEGATION)
        if p >= 0:
            return MBF.onp(expr[:p] + expr[p + 1:]) + expr[p]

        return expr

    @staticmethod
    def map(expr, vec):
        letters = (set(expr) & set(MBF.VAR)) | set(MBF.VAL)

        sorted_letters = "".join(sorted(list(letters)))
        vec = "01" + vec
        expr = list(expr)

        for index, char in enumerate(expr):
            pos = sorted_letters.find(char)
            if pos != -1:
                expr[index] = vec[pos]

        return "".join(expr)

    @staticmethod
    def generate_sequences(n):
        for m in range(2 ** n):
            yield bin(m)[2:].rjust(n, "0")

    @staticmethod
    def valuate(expr):
        stack = []
        for char in expr:
            if char in "01":
                stack.append(int(char))
            elif char == MBF.OPERATORS[0]:
                stack.append((1 - stack.pop()) | stack.pop())
            elif char == MBF.OPERATORS[1]:
                stack.append(stack.pop() & stack.pop())
            elif char == MBF.OPERATORS[2]:
                stack.append(stack.pop() | stack.pop())
            elif char == MBF.OPERATORS[3]:
                stack.append(1 - (stack.pop() & stack.pop()))
            elif char == MBF.OPERATORS[4]:
                a = stack.pop()
                b = stack.pop()
                stack.append(((1 - a) & b) | (a & (1 - b)))
            elif char == MBF.NEGATION:
                stack.append(1 - stack.pop())
        return stack[0]

    @staticmethod
    def tautology(expr):
        n = len(set(expr) & set(MBF.VAR))
        for i in MBF.generate_sequences(n):
            if not MBF.valuate(MBF.map(MBF.onp(expr), i)):
                return False
        return True

    def expr_to_set(self):
        res = set()
        for seq in MBF.generate_sequences(len(set(self.expr) & set(MBF.VAR))):
            if MBF.valuate(MBF.map(MBF.onp(self.expr), seq)) == 1:
                res.add(seq)
        return res

    def vector_to_func(self, vectors):
        func = ''
        for vec in vectors:
            tmp = ""
            for i, var in enumerate(vec):
                if var == '~':
                    continue
                if var == '0':
                    tmp += MBF.negate(self.labels[i])
                else:
                    tmp += self.labels[i]
                tmp += "&"

            tmp = tmp[:-1]
            if len(tmp) > 2:
                func += "(" + tmp + ")"
            else:
                func += tmp
            func += "|"
        return func[:-1]

    @staticmethod
    def combine(w1, w2):
        n = len(w1)
        counter = 0
        res = ""
        for i in range(n):
            if w1[i] != w2[i]:
                counter += 1
                res += "~"
            else:
                res += w1[i]
        if counter != 1:
            return None
        return res

    @staticmethod
    def reduce(data):
        flag2 = False
        s = set()
        for x1 in data:
            flag = False
            for x2 in data:
                w = MBF.combine(x1, x2)
                if w:
                    s.add(w)
                    flag = True
            if not flag:
                flag2 = True
                s.add(x1)

        if not flag2:
            return MBF.reduce(s)
        return s

    @staticmethod
    def match(vec, pattern):
        n = len(vec)
        for i in range(n):
            if pattern[i] == "~":
                continue
            if vec[i] != pattern[i]:
                return False
        return True

    @staticmethod
    def minimum(vec_set, patt_set):
        for size in range(1, len(patt_set) + 1):
            for comb in combinations(patt_set, size):
                tmp = set()
                for vec in vec_set:
                    for patt in comb:
                        if MBF.match(vec, patt):
                            tmp.add(vec)

                if len(tmp) == len(vec_set):
                    return comb

    # ----------------------------------------------------- #

    def simplify_xor(self):
        """Funkcja upraszczająca wyrażenie poprzez wyszukiwanie możliwych przekształceń wyrażenia z użyciem operatora xor """
        available = [True] * (len(self.vec_list) + 1)

        def inside_f():
            for i, vec in enumerate(self.vec_list):
                if not available[i]:
                    continue
                for j, s in enumerate(vec):

                    if s not in "01":
                        continue
                    k = j + 1

                    while k < len(vec):

                        if vec[k] in "01":

                            value = "1"
                            if vec[j] == vec[k]:
                                value = "0"

                            opposite = next((x for x in list(compress(self.vec_list, available)) if
                                             x == vec[:j] + str(1 - int(vec[j])) + vec[j + 1:k] + str(
                                                 1 - int(vec[k])) + vec[k + 1:]), None)

                            if opposite is not None:
                                label = self.labels[j] + "^" + self.labels[k]
                                l_index = next((x for x in self.labels if x == label), None)
                                available[self.vec_list.index(opposite)] = False

                                if l_index is None:
                                    self.labels.append(label)
                                    l_index = len(self.labels) - 1
                                    for l, _ in enumerate(self.vec_list):
                                        self.vec_list[l] += "~"
                                else:
                                    l_index = self.labels.index(l_index)

                                self.vec_list[i] = vec[:j] + "~" + vec[j + 1:k] + "~" + vec[
                                                                                        k + 1:l_index] + value + vec[
                                                                                                                 l_index + 1:]

                                return inside_f()
                        k += 1

        inside_f()
        self.vec_list = list(compress(self.vec_list, available))

    def simplify_alternatives(self):
        """Funkcja upraszczająca wyrażenie poprzez wyszukiwanie składowych alternatyw, które mogą zostać połączone """
        available = [True] * (len(self.vec_list) + 1)

        def inside_f():
            for i, vec in enumerate(self.vec_list):
                if not available[i]:
                    continue
                for j, s in enumerate(vec):
                    if s not in "01":
                        continue

                    opposite = next((x for x in list(compress(self.vec_list, available)) if
                                     x == vec[:j] + str(1 - int(vec[j])) + vec[j + 1:]),
                                    None)
                    if opposite is not None:
                        available[self.vec_list.index(opposite)] = False
                        self.vec_list[i] = vec[:j] + "~" + vec[j + 1:]

                        return inside_f()

        inside_f()
        self.vec_list = list(compress(self.vec_list, available))

    def simplify_Shaffter(self):
        """Funkcja upraszczająca wyrażenie poprzez wyszukiwanie możliwych przekształceń wyrażenia z użyciem operatora dysjunkcji Shafftera """
        available = [True] * (len(self.vec_list) + 1)

        def inside_f():
            for i, vec in enumerate(self.vec_list):
                if not available[i]:
                    continue
                for j, s in enumerate(vec):
                    if s != "0":
                        continue

                    for k in range(len(vec)):
                        if k == j:
                            continue

                        l_vec = list(vec)
                        l_vec[j] = "~"
                        l_vec[k] = "0"

                        next_vec = "".join(l_vec)

                        opposite = next((x for x in list(compress(self.vec_list, available)) if
                                         x == next_vec),
                                        None)
                        if opposite is not None:
                            label = self.labels[j] + "/" + self.labels[k]
                            l_index = next((x for x in self.labels if x == label), None)
                            available[self.vec_list.index(opposite)] = False

                            if l_index is None:
                                self.labels.append(label)
                                l_index = len(self.labels) - 1
                                for l, _ in enumerate(self.vec_list):
                                    self.vec_list[l] += "~"
                            else:
                                l_index = self.labels.index(l_index)

                            if k > j:
                                self.vec_list[i] = vec[:j] + "~" + vec[j + 1:k] + "~" + vec[k + 1:l_index] + "1" + vec[
                                                                                                                   l_index + 1:]
                            else:
                                self.vec_list[i] = vec[:k] + "~" + vec[k + 1:j] + "~" + vec[j + 1:l_index] + "1" + vec[
                                                                                                                   l_index + 1:]

                            return inside_f()

        inside_f()
        self.vec_list = list(compress(self.vec_list, available))

    def simplify_implication(self):
        """Funkcja upraszczająca wyrażenie poprzez wyszukiwanie możliwych przekształceń wyrażenia z użyciem operatora implikacji """
        available = [True] * (len(self.vec_list) + 1)

        def inside_f():
            for i, vec in enumerate(self.vec_list):
                if not available[i]:
                    continue
                for j, s in enumerate(vec):
                    if s != "1":
                        continue

                    for k in range(len(vec)):
                        if k == j:
                            continue

                        l_vec = list(vec)
                        l_vec[j] = "~"
                        l_vec[k] = "0"

                        next_vec = "".join(l_vec)

                        opposite = next((x for x in list(compress(self.vec_list, available)) if
                                         x == next_vec),
                                        None)
                        if opposite is not None:
                            label = "(" + self.labels[k] + ">" + self.labels[j] + ")"
                            l_index = next((x for x in self.labels if x == label), None)
                            available[self.vec_list.index(opposite)] = False

                            if l_index is None:
                                self.labels.append(label)
                                l_index = len(self.labels) - 1
                                for l, _ in enumerate(self.vec_list):
                                    self.vec_list[l] += "~"
                            else:
                                l_index = self.labels.index(l_index)

                            if k > j:
                                self.vec_list[i] = vec[:j] + "~" + vec[j + 1:k] + "~" + vec[k + 1:l_index] + "1" + vec[
                                                                                                                   l_index + 1:]
                            else:
                                self.vec_list[i] = vec[:k] + "~" + vec[k + 1:j] + "~" + vec[j + 1:l_index] + "1" + vec[
                                                                                                                   l_index + 1:]
                            return inside_f()

        inside_f()
        self.vec_list = list(compress(self.vec_list, available))

    @staticmethod
    def negate(expr):
        if len(expr) == 1:
            return MBF.NEGATION + expr
        else:
            return MBF.NEGATION + "(" + expr + ")"
