############################################################
# CMPSC 442: Homework 4
############################################################

student_name = "Jonathan Augustin"

############################################################
# Imports
############################################################

# Include your imports here, if any are used.
import itertools as it

############################################################
# Section 1: Propositional Logic
############################################################

class Expr(object):
    def __hash__(self):
        return hash((type(self).__name__, self.hashable))

class Atom(Expr):
    def __init__(self, name):
        self.name = name
        self.hashable = name
    def __eq__(self, other):
        if isinstance(other, Atom):
            return (self.name == other.name)
        return False
    def __repr__(self):
        return "Atom(" + str(self.name) + ")"
    def atom_names(self):
        return set([self.name])
    def evaluate(self, assignment):
        if (assignment[self.hashable] == True):
            return True
        else:
            return False
    def to_cnf(self):
        return self
    def __hash__(self):
        return hash(repr(self))

class Not(Expr):
    def __init__(self, arg):
        self.arg = arg
        self.hashable = arg
    def __eq__(self, other):
        if isinstance(other, Not):
            return (self.arg == other.arg)
        return False
    def __repr__(self):
        return "-(" + str(self.arg) + ")"
    def atom_names(self):
        return self.arg.atom_names()
    def evaluate(self, assignment):
        return not self.arg.evaluate(assignment)
    def to_cnf(self):
        if isinstance(self.arg, Not):
            return self.arg
        elif isinstance(self.arg, And):
            return Or(Not(self.arg[0]), Not(self.arg[1]))
        elif isinstance(self.arg, Or):
            array = []
            for function in self.arg.disjuncts:
                array.append(function)
            return And(Not(array[0]), Not(array[1]))
    def __hash__(self):
        return hash(repr(self))

        
class And(Expr):
    def __init__(self, *conjuncts):
        self.conjuncts = conjuncts
        self.hashable = self.conjuncts
    def __eq__(self, other):
        for conjunct in self.conjuncts:
            for other_conjuct in range(len(other.conjuncts)):
                truth = bool(conjunct == other.conjuncts[other_conjuct])
                if truth == True:
                    break
                if truth == False and other_conjuct == (len(other.conjuncts)-1):
                    return False
        return True
    def __repr__(self):
        string = '('
        i = 0
        for conjunct in self.conjuncts:
            string += conjunct.__repr__() + ' '
            if i < (len(self.conjuncts)-1):
                string += 'A '
            i+=1
        string += ')'
        return string
    def atom_names(self):
        names = {}
        for element in self.conjuncts:
            if names == {}:
                names = element.atom_names()
            else:
                names = element.atom_names() | names
        return names
    def evaluate(self, assignment):
        truthTable = [(self.conjuncts[expr].evaluate(assignment)) for expr in range(len(self.conjuncts))]
        for i in range(len(truthTable)):
            if truthTable[i] == True:
                if i == len(self.conjuncts)-1:
                    return truthTable[i]
                continue
            else:
                return truthTable[i]
    def to_cnf(self):
        if isinstance(self.conjuncts[1], Or):
            return Or(And(self.conjuncts[0], self.conjuncts[1][0]), And(self.conjuncts[0], self.conjuncts[1][1]))
        else:
            return And(self.conjuncts[0].to_cnf(), self.conjuncts[1].to_cnf())

    def __hash__(self):
        return hash(repr(self))

class Or(Expr):
    def __init__(self, *disjuncts):
        self.disjuncts = frozenset(disjuncts)
        self.hashable = self.disjuncts
    def __eq__(self, other):
        for disjunct in self.disjuncts:
            length = 0
            for other_disjunct in other.disjuncts:
                truth = bool(disjunct == other_disjunct)
                if truth == True:
                    break
                if truth == False and length == (len(other.disjuncts)-1):
                    return False
                length +=1
        return True
    def __repr__(self):
        string = '('
        i = 0
        for disjunct in self.disjuncts:
            string += disjunct.__repr__() + ' '
            if i < (len(self.disjuncts)-1):
                string += 'V '
            i+=1
        string += ")"
        return string
    def atom_names(self):
        names = {}
        for element in self.disjuncts:
            if names == {}:
                names = element.atom_names()
            else:
                names = element.atom_names() | names
        return names
    def evaluate(self, assignment):
        truthTable = [expr.evaluate(assignment) for expr in (self.disjuncts)]
        for i in range(len(truthTable)):
            if truthTable[i] == False:
                if i == len(self.disjuncts):
                    return truthTable[i]
                continue
            else:
                return truthTable[i]
    def to_cnf(self):
        array = []
        array2 = []
        for function in self.disjuncts:
            array.append(function)
        for function2 in self.disjuncts[1]:
            array2.append(function2)
        if isinstance(array[1], And):
            return And(Or(array[0], array2[0]), Or(array[0], array2[1]))
        else:
            return Or(array[0].to_cnf(), array[1].to_cnf())
    def __hash__(self):
        return hash(repr(self))

class Implies(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)
    def __eq__(self, other):
        if (self.left == other.left and self.right == other.right):
            return True
        return False
    def __repr__(self):
        string = '(' + repr(self.left) + ' => ' + repr(self.right) + ')'
        return string
    def atom_names(self):
        names = self.left.atom_names() | self.right.atom_names()
        return names
    def evaluate(self, assignment):
        if (self.left.evaluate(assignment) == True):
            if self.right.evaluate(assignment) == False:
                return False
        return True
    def to_cnf(self):
        return Not(Or(self.left, self.right)).to_cnf()
    def __hash__(self):
        return hash(repr(self))

class Iff(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)
    def __eq__(self, other):
        if (self.left == other.left and self.right == other.right):
            return True
        return False
    def __repr__(self):
        string = '(' + repr(self.left) + ' <=> ' + repr(self.right) + ')'
        return string
    def atom_names(self):
        names = self.left.atom_names() | self.right.atom_names()
        return names
    def evaluate(self, assignment):
        if (self.left.evaluate(assignment) != self.right.evaluate(assignment)):
            return True
        return False
    def to_cnf(self):
        return And(Implies(self.left, self.right), Implies(self.right, self.left)).to_cnf()
    def __hash__(self):
        return hash(repr(self))

def satisfying_assignments(expr):
    names = {}
    for element in expr.hashable:
        if names == {}:
            names = element.atom_names()
        else:
            names = element.atom_names() | names
    product = list(it.product([True, False], repeat= len(names)))
    for truth in product:
        assignment = {}
        i = 0
        for name in names:
            update = {name: truth[i]}
            assignment.update(update)
            i+=1
        if(expr.evaluate(assignment)== True):
            yield assignment

class KnowledgeBase(object):
    def __init__(self):
        pass
    def get_facts(self):
        pass
    def tell(self, expr):
        pass
    def ask(self, expr):
        pass
