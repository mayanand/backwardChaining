#!/usr/bin/env python

import re
import copy
import sys
import pdb

class kb(object):
    def __init__(self, clauses = {}):
        
        self.clauses = clauses
        # self.clauses = {
        #     'F': [('y,x', 'G(x,y)')],
        #     'G': [('SS,S', 'True'), ('x,y', 'F(S,SS)')],
        # }
        # self.clauses = {
        # 'H' : [('x', 'A(x)'), ('x', 'R(x)'), ('x', 'G(x)')],
        # '~H' : [('y', 'D(x,y)')],
        # 'A' : [('x', 'B(x,y) ^ C(x,y)')],
        # 'C' : [('x,y', 'D(x,y) ^ Q(y)')],
        # 'G' : [('x','F(x)')],
        # 'F' : [('x','H(x)')],
        # 'B' : [('John,Alice', 'True'), ('John,Bob', 'True')],
        # 'D' : [('John,Alice', 'True'), ('John,Bob', 'True')],
        # 'R' : [('Tom', 'True')],
        # 'Q' : [('Bob', 'True')],
        # }
        
        # self.clauses = {
        #     'C': [('x,w', 'A(x,y) ^ B(z,w)')],
        #     'A': [('x,y', 'C(y,x)'), ('EE,CS', 'True')],
        #     'B': [('y,x', 'C(x,y)'), ('MS,PHD', 'True')],
        # }

 
        # self.clauses = {
        #     'Fly': [('y', 'G(y,b) ^ Fly(x) ^ Friend(x,b) ^ H(y)'), ('x', 'Parent(x,y) ^ Hero(y)') ],
        #     'H': [('Tom)', 'True'), ('Ram', 'True'), ('Cruise', 'True'), ('Pilot', 'True')],
        #     'G': [('Ram, Ram', 'True'), ('Cruise,Cruise', 'True'), ('Tom,Tom', 'True'), ('Pilot,Pilot', 'True')],
        #     'Parent': [('Dr,Doom', 'True')],
        #     'Hero': [('Doom', 'True')],
        #     'Friend': [('Dr,Pilot', 'True'), ('Pilot,Tom', 'True'), ('Tom,Cruise', 'True'), ('Cruise,Ram', 'True')]
        # }
        
        # self.clauses = {
        #     'Uncle': [('x,z', 'Male(x) ^ Parent(m,z) ^ Sibling(x,m)')],
        #     'Father': [('x,y', 'Parent(x,y)'), ('Shawn,John', 'True'), ('Suresh,Ramesh', 'True'), ('Shawn,Neelu', 'True')],
        #     'Mother': [('x,y', 'Parent(x,y)'), ('Kill,Bill', 'True'), ('Neelu,Sarah', 'True')],       
        #     'Sibling': [('p,w', 'Parent(x,p) ^ Parent(x,w) ^ Parent(a,b) ^ Parent(c,d)')]
        # }
        
        self.regex = re.compile('(\S+)\((.*?)\)')   #hard coding the values here
        self.visitedClauses = []
        self.std_ctr = 1
        self.std_rules = {}
    
        
    def infer(self, goalList, theta = {}):
        answers = {}        #local variable
        
        if len(goalList) == 0:
            # print "VISITED CLAUSES"
            # print self.visitedClauses
            # print "~~~~~~~~~~~~~~~~~~~~returning tfrom terminal condition with value of theta as: ", theta
            return theta
        
        quest = goalList.pop(-1)
        # print "this is quest, goal list and theta", quest, goalList, theta
        
        m = re.match(self.regex, quest)
        predicate = m.group(1)
        predArgs = m.group(2)
        predArgsList = predArgs.split(",")
        
        qDash = self.replaceWithTheta(predArgsList, theta)
        
        # print "qdash isconstant", qDash, self.isConstantQuery(qDash)
        # print "visted clauses", self.visitedClauses
        constantQuery = predicate + '(' + qDash + ')'
        if self.isConstantQuery(qDash):
            if constantQuery not in self.visitedClauses:
                if not self.isFact(predicate, qDash):
                    self.visitedClauses.append(constantQuery)
            else:
                return answers
        
        newGoalList = copy.deepcopy(goalList)
            
        if predicate in self.clauses:
            
            # print "printig all predicates"
            # print  self.clauses[predicate]
            
            #this is or node. so one of them has to be correct
            for rule in self.clauses[predicate]:        
                lhs = self.standardizeApart(rule)
                # print "prinitng lhs"
                # print lhs
                arguments =  lhs[0].split(',')
                thetaDash = self.unify(arguments, qDash.split(','))
                # print '*******************'
                # print thetaDash, type(thetaDash), bool(thetaDash)
                
                if thetaDash != 'False':       #check whether unification succeeds
                    if lhs[1] != 'True':
                        # print "the conjunctive clause"
                        # print conjunctiveClauses
                        conjunctiveClauses = [x.strip() for x in lhs[1].split("^")]
                        newGoalList.extend(conjunctiveClauses)     #adding new goals to goal list
                    composedTheta = self.compose(thetaDash, theta)
                        #unify answers here    
                    # print "----> answers, thetaDash, theta, composedTheta, newGoalList"
                    # print answers, thetaDash, theta, composedTheta, newGoalList
                    answers.update(self.infer(newGoalList, composedTheta))                    
                    # print "priting ansers", answers
                else:
                    # print 'passing here as unification could not be done'        
                    pass
            return answers
        return answers
    
        
    
    def isVariableInQuestArgs(self, questArgs):
        """
            @param: questArgs is a list which contains the arguments of quest
            helper fucntion to check if genrator is needed
            returns True if variable found else return False
        """
        
        for arg in questArgs:
            if self.isVariable(arg):
                return True
        return False
    
    
    def replaceWithTheta(self, expr, thetaDict):
        
        """
            helper function to replace the expression with unified expression
            @param: list of strings as arguments
                    thetaDict is a dict
            returns the subtituted expression
        """
        
        newExprList = []
        for item in expr:
            visitedNode = []
            if item in thetaDict:
                value = thetaDict[item]
                
                while self.isVariable(value):
                    if value not in visitedNode:
                        visitedNode.append(value)
                    else:
                        value = thetaDict.get(value, value)
                        break

                newExprList.append(value)      
            else:
                newExprList.append(item)
        
        newExpr = ','.join(newExprList)
        
        return newExpr
    
    
    def isVariable(self, string):
        
        """
            @param: string
            helper function to check if the token is a variable or not.
            return True if it is a variable else returns False
        """
        
        regex = re.compile("^[a-z]")
        m = re.match(regex, string)
        
        if m:
            return True
        else:
            return False
    
    
    def unify(self, argumentList, constantList):
        #need to standerdize here before unification      
        """
            function to unify arguments of 2 instances of a predicate
            with each other
            @param: argumentList -> list containing arguments with variables instance
                    constantList -> list containing arguments with constants and variables
                    unifierDict is empty by default
            returns the uninfied dict if unification was possible
                    else returns False
        """
        counter = 0
        unifierDict = {}
        
        # print "-------------> inside unify"
        # print argumentList, constantList
        
        for item in argumentList:
            
            if (self.isVariable(item) and self.isVariable(constantList[counter])):
                if constantList[counter] in unifierDict:
                    unifierDict[unifierDict[constantList[counter]]] = item
                else:    
                    unifierDict[constantList[counter]] = item #replace one variable by another
            elif (not self.isVariable(item) and self.isVariable(constantList[counter])):
                if constantList[counter] in unifierDict:
                    if unifierDict[constantList[counter]] != item:
                        return 'False'
                else:
                    unifierDict[constantList[counter]] = item
            elif (self.isVariable(item) and  not self.isVariable(constantList[counter])):
                if item in unifierDict:
                    if unifierDict[item] != constantList[counter]:
                        return 'False'
                else:
                    unifierDict[item] = constantList[counter]
            elif (item == constantList[counter]):
                pass
            else:   #in this case both are constants and hence cant be unified
                return 'False'
            counter += 1
        # print "True inside the unifier"
        # print unifierDict
        return unifierDict
    
    def standardizeApart(self, rule):
        
        # print '--------------------?'
        # print "printing std rules and rule"
        # print self.std_rules, rule
        
        # if rule[1] == 'True':
        #     return rule
        
        stdDict = {}
        standardizedPredList = []
        #rule = ('x', 'A(x)')
        lhsVarList = rule[0].split(',')
        
        for var in lhsVarList:
            if (not var in stdDict and self.isVariable(var)):
                stdDict[var] = var + str(self.std_ctr)
                self.std_ctr += 1
        
        if rule[1] == 'True':
            return rule
        else:
            conjunctiveClauses = [x.strip() for x in rule[1].split("^")]
            for clause in conjunctiveClauses:
                m = re.match(self.regex, clause)
                if m:
                    predicate = m.group(1)
                    predArgs = m.group(2)
                    predArgsList = predArgs.split(",")
                    
                    for rVar in predArgsList:
                        if (not rVar in stdDict and self.isVariable(rVar)):
                            stdDict[rVar] = rVar + str(self.std_ctr)
                            self.std_ctr += 1
                    
        #            print stdDict        
                    
                    standardizedPred = predicate + '(' + ','.join(map(str, [stdDict.get(x, x) for x in predArgsList])) + ')'
                    standardizedPredList.append(standardizedPred)
        
        resLHSZero = ','.join(map(str, [stdDict.get(x, x) for x in lhsVarList]))
        resLHSOne = ' ^ '.join(map(str, standardizedPredList))
        
        resTuple = (resLHSZero, resLHSOne)
        
        # print resTuple
        # self.std_rules[rule] = copy.deepcopy(resTuple)
        return resTuple
    
    def compose(self, thetaOne, thetaTwo):    
        
        sc = {}
        for k, v in thetaOne.iteritems():
            if v in thetaTwo:
                w = thetaTwo[v]
                sc[k] = w 
            else:
                sc[k] = v
        for k, v in thetaTwo.iteritems():
            if not k in thetaOne:
                sc[k] = v
            
        return sc
    
    def isFact(self, pred, argString):
        """
            @params: pred is the predicate of the query
                     argString is the comma separate string or arguments
            returns true if it is a fact else returns false
        """
        if pred in self.clauses:
            for clause in self.clauses[pred]:
                if argString == clause[0] and clause[1] == 'True':
                    return True
        
        return False
                
        
    def isConstantQuery(self, arguments):
        """
         helper function to check if all the arguments are constants or not.
         @param: arguments is a comma separated string consisting of all arguments
         returns True is all te arguments are constant else returns false
        """
        argList = arguments.split(',')
         
        for arg in argList:
            if self.isVariable(arg):
                return False
        return True

def processRawRules(ruleList):
    
    import collections
    ruleDict = collections.defaultdict(list)
    regex = re.compile('(\S+)\((.*?)\)')   #hard coding the values here
    for raw in ruleList:
        splitRule = [x.strip() for x in raw.split("=>")]
        if len(splitRule) > 1:
            m = re.match(regex, splitRule[1])
            ruleDict[m.group(1)].append((m.group(2), splitRule[0]))
        elif len(splitRule) == 1:
            m = re.match(regex, splitRule[0])
            ruleDict[m.group(1)].append((m.group(2), 'True'))
        else:
            print "the input data has issues"
    return ruleDict


def parse(inputFH):
    queryList = []
    noOfQuery = int(inputFH.readline())
    for x in xrange(0, noOfQuery):
        queryList.append(inputFH.readline().strip('\n'))
    noOfRules = int(inputFH.readline())
    rawRules = [x.strip('\n') for x in inputFH.readlines()]
    processedRule = processRawRules(rawRules)
    
    return processedRule, queryList
    
    
    
    
    
if __name__ == "__main__":
    
    print sys.argv
    fileName = str(sys.argv[-1])
    file_handle = open(fileName,'r')
    opFH = open("output.txt","w")
    processedRule, queryList = parse(file_handle)
    
    # print '&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&'
    # print processedRule
    # print queryList

    kb_obj = kb(processedRule)
    
    # strList = ['x2', 'x3']
    # thetaDit = {'x2':'x3', 'x3':'Sara'}
    # print kb_obj.replaceWithTheta(strList, thetaDit)
    
    for query in queryList:
        kb_obj.visitedClauses = []
        goalList = []
        goalList.append(query)
        final = {}
        try:
            final = kb_obj.infer(goalList)
        except Exception as e:
            print '!!!!!!!!!!!! exception: ', e
            print 'I just want to avoid a crash and print false in this case'
        #write a try catch thing here to ensure that we always get an output
        ans = 'FALSE'
        if final:
            ans = 'TRUE'
        opFH.write(ans + '\n')
        print "##############################"
        
    
    opFH.close()
    # final = kb_obj.infer(["Uncle(John,Sarah)"], {})
    # print "printing final"
    # print final
    

    
    