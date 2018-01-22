import pickle as cPickle,bisect
import time

class KnowledgeBase:

    def __init__(self):
        self.sentences = []
        self.variables = {}
        self.constants = {}
        self.standardisation_counter = 0

    def ask(self, query):
        query = self.parseQuery(query)
        return self.resolution(query)

    def resolution(self,query):
        self.sentences.insert(0,query)
        newSet = set()
        while True:
            n = len(self.sentences)
            for i in range(0,n):
                for j in range(i+1,n):
                    if time.time() >= timeout:
                        return "FALSE"
                    resolvents = self.resolve(self.sentences[i], self.sentences[j])
                    if False in resolvents:
                        return "TRUE"
                    newSet.update(set(resolvents))
            if newSet.issubset(set(self.sentences)):
                return "FALSE"
            for c in newSet:
                if c not in self.sentences:
                    self.sentences.append(c)


    def resolve(self,si,sj):
        clauses = []
        for pi in si.predicates:
            if pi.name in sj.names:
                for pj in sj.predicates:
                    if pi.type != pj.type and pi.canUnify(pj):
                        subst = self.unify(pj,pi,{})
                        if type(subst) == dict and subst is not False:
                            itemp = cPickle.loads(cPickle.dumps(si.predicates, -1))
                            jtemp = cPickle.loads(cPickle.dumps(sj.predicates, -1))
                            del itemp[si.predicates.index(pi)]
                            del jtemp[sj.predicates.index(pj)]
                            temp = itemp + jtemp
                            dnew = self.substitution(temp,subst)
                            dnewnames = []
                            for i in range(0,len(dnew)):
                                dnewnames.append(dnew[i].name)
                            if len(dnew) !=0:
                                clauses.append(Sentence(dnew,dnewnames))
                            else:
                                clauses.append(False)
        return clauses



    def substitution(self,predicates,theta):
        for variable in theta:
            for p in predicates:
                try:
                    p.arguments[p.arguments.index(variable)] = theta.get(variable)
                except ValueError:
                    pass
                if variable in p.variables:
                    if theta.get(variable)[0].islower():
                        p.variables.setdefault(theta.get(variable),p.variables.get(variable))
                        del p.variables[variable]
                    else:
                        del p.variables[variable]
                        p.constants.setdefault(theta.get(variable),Constant(theta.get(variable)))
        return predicates

    def unify(self,query,sentence,theta):
        if theta == False:
            return False
        elif query == sentence:
            return theta
        elif type(query) == str and query[0].islower():
            return self.unifyVar(query,sentence,theta)
        elif type(sentence) == str and sentence[0].islower():
            return self.unifyVar(sentence,query,theta)
        elif type(query) == Predicate and type(sentence) == Predicate:
            return self.unify(query.arguments,sentence.arguments,self.unify(query.name,sentence.name,theta))
        elif type(query) == list and type(sentence) == list:
            return self.unify(query[1:],sentence[1:],self.unify(query[0],sentence[0],theta))
        else:
            return False



    def unifyVar(self,var,x,theta):
        if var in theta:
            return self.unify(theta.get(var),x,theta)
        elif x in theta:
            return self.unify(var,theta.get(x),theta)
        elif self.occurs_check(var,x):
            return False
        else:
            theta.setdefault(var,x)
            return theta


    def occurs_check(self,v, x):
        if type(x) == str and x[0].islower():
            if v == x:
                return True
        else:
            False

    def parseQuery(self,query):
        predicates = []
        names = []
        atoms = query.split('|')
        for atom in atoms:
            atom = atom.strip()
            constants = {}
            variables = {}
            if atom[0] == '~':
                type = -1
                predicateName = atom[1:atom.index('(')].strip()
            else:
                type = 1
                predicateName = atom[:atom.index('(')].strip()
            arguments = atom[atom.index('(')+1:atom.index(')')].replace(' ', '').split(",")
            numberOfArguments = len(arguments)
            for arg in arguments:
                arg = arg.strip()
                if arg[0].isupper():
                    constant = Constant(arg)
                    constants.setdefault(arg,constant)
                else:
                    variable = Variable(arg)
                    variables.setdefault(arg,variable)
            predicates.append(Predicate(predicateName,type,numberOfArguments,arguments,constants,variables))
            names.append(predicateName)
        return Sentence(predicates,names)

    def tell(self,sentence):
        sentence =  self.parse(sentence)
        self.sentences.append(sentence)

    def parse(self,sentence):
        predicates = []
        names = []
        sentence_variables = {}
        atoms = sentence.split('|')
        for atom in atoms:
            atom = atom.strip()
            constants = {}
            variables = {}
            if atom[0] == '~':
                type = -1
                predicateName = atom[1:atom.index('(')].strip()
            else:
                type = 1
                predicateName = atom[:atom.index('(')].strip()
            arguments = (atom[atom.index('(')+1:atom.index(')')]).replace(' ', '').split(",")
            numberOfArguments = len(arguments)
            for arg in arguments:
                arg = arg.strip()
                if arg[0].isupper():
                    constant = Constant(arg)
                    constants.setdefault(arg,constant)
                    self.constants.setdefault(arg,constant)
                else:
                    if arg in self.variables and arg not in sentence_variables:
                        new_arg = self.generateStandardizedVariable()
                        variable = Variable(new_arg)
                        variables.setdefault(new_arg,variable)
                        sentence_variables.setdefault(arg,variable)
                        self.variables.setdefault(new_arg,variable)
                        arguments[arguments.index(arg)] = new_arg
                    elif arg in self.variables and arg in sentence_variables:
                        variable = sentence_variables.get(arg)
                        new_arg = variable.name
                        arguments[arguments.index(arg)] = new_arg
                        variables.setdefault(new_arg,variable)
                    else:
                        variable = Variable(arg)
                        variables.setdefault(arg,variable)
                        sentence_variables.setdefault(arg,variable)
                        self.variables.setdefault(arg,variable)
            predicates.append(Predicate(predicateName,type,numberOfArguments,arguments,constants,variables))
            names.append(predicateName)
        return Sentence(predicates,names)

    def generateStandardizedVariable(self):
        standardizedVariable = 'x'+ str(self.standardisation_counter)
        self.standardisation_counter += 1
        return standardizedVariable

class Predicate:
    def __init__(self,name,type,numberOfArguments,arguments,constants,variables):
        self.name = name
        self.type = type
        self.numOfArguments = numberOfArguments
        self.arguments = arguments
        self.constants = constants
        self.variables = variables

    def __str__(self):
        return self.name + " " + str(self.type)+" "+str(self.arguments)


    def canUnify(self, other):
        if self.name != other.name:
            return False
        if self.numOfArguments != other.numOfArguments:
            return False

        for i in range(self.numOfArguments):
            if self.arguments[i][0].isupper() and other.arguments[i][0].isupper() and self.arguments[i] != other.arguments[i]:
                return False

        return True



class Constant:
    def __init__(self,value):
        self.value = value


class Variable:
    def __init__(self,name):
        self.name = name
        self.value = ""


class Sentence:
    def __init__(self,predicates,names):
        self.predicates = predicates
        self.names = names
        self.hashcode = self.setHash()

    def setHash(self):
        s = ""
        for p in self.predicates:
            s += str(p)
        return hash(s)

    def __hash__(self):
        return self.hashcode

    def __eq__(self, other):
        if type(self) != type(other):
            return False
        return self.hashcode == other.hashcode



class Query:
    def __init__(self,query):
        self.query = query

kb = KnowledgeBase()
queries = []
with open('input.txt') as input_file:
    numberOfQueries = int(input_file.readline().rstrip('\n'))
    for i in range(numberOfQueries):
        line = input_file.readline().rstrip('\n')
        if line[0] == '~':
            line = line[1:]
        else:
            line = '~'+line
        queries.append(line)
    numberOfGivenSentences = int(input_file.readline().rstrip('\n'))
    for i in range(numberOfGivenSentences):
        line = input_file.readline().rstrip('\n')
        kb.tell(line)

with open('output.txt', 'w') as output_file:
    for query in queries:
        tempKB = cPickle.loads(cPickle.dumps(kb, -1))
        timeout = time.time() + 20
        answer = tempKB.ask(query)
        output_file.write(answer+'\r\n')