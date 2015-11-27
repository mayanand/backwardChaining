#!/usr/bin/env python

import re
import copy

class kb(object):
    def __init__(self, initialKb = []):
        # self.facts = {
        # 'B' : ["(John,Alice)", "(John,Bob)"],
        # 'D' : ["(John,Alice)", "(John,Bob)"],
        # 'R' : ["(Tom)"],
        # 'Q' : ["(Bob)"],
        # }
            
        self.clauses = {
        'H' : [('x', 'A(x)'), ('x', 'R(x)'), ('x', 'G(x)')],
        '~H' : [('y', 'D(x,y)')],
        'A' : [('x', 'B(x,y) ^ C(x,y)')],
        'C' : [('x,y', 'D(x,y) ^ Q(y)')],
        'G' : [('x','F(x)')],
        'F' : [('x','H(x)')],
        'B' : [('John,Alice', 'True'), ('John,Bob', 'True')],
        'D' : [('John,Alice', 'True'), ('John,Bob', 'True')],
        'R' : [('Tom', 'True')],
        'Q' : [('Bob', 'True')],
        }
        
        self.regex = re.compile('(\S+)\((.*?)\)')   #hard coding the values here
        self.visitedClauses = []
    
        
    def infer(self, goalList, theta):
        answers = {}        #local variable
        
        if len(goalList) == 0:
            print "~~~~~~~~~~~~~~~~~~~~returning tfrom terminal condition with value of theta as: ", theta
            return theta
        
        quest = goalList.pop(-1)
        print "this is quest, goal list and theta", quest, goalList, theta
        
        #lhsRegex = re.compile('(\w+)(.*)')
        m = re.match(self.regex, quest)
        predicate = m.group(1)
        predArgs = m.group(2)
        predArgsList = predArgs.split(",")
        #print '************** predargs'
        #print predArgs
        
        qDash = self.replaceWithTheta(predArgs, theta)
        
        print "qdash isconstant", qDash, self.isConstantQuery(qDash)
        print "visted clauses", self.visitedClauses
        constantQuery = predicate + '(' + qDash + ')'
        if self.isConstantQuery(qDash):
            if constantQuery not in self.visitedClauses:
                self.visitedClauses.append(constantQuery)
            else:
                return answers
        
            
        if predicate in self.clauses:
            print "printig all predicates"
            print  self.clauses[predicate]
            
            #this is or node. so one of them has to be correct
            for lhs in self.clauses[predicate]:        

                print "prinitng lhs"
                print lhs
                #need to standerdize the variables here before proceeding
                arguments =  lhs[0].split(',')
                thetaDash = self.unify(arguments, qDash.split(','))
                print '*******************'
                print thetaDash, type(thetaDash), bool(thetaDash)
                newGoalList = copy.deepcopy(goalList)
                
                if thetaDash != 'False':       #check whether unification succeeds
                    if lhs[1] != 'True':
                        # print "the conjunctive clause"
                        # print conjunctiveClauses
                        conjunctiveClauses = [x.strip() for x in lhs[1].split("^")]
                        newGoalList.extend(conjunctiveClauses)     #adding new goals to goal list
                    composedTheta = self.compose(thetaDash, theta)
                        #unify answers here    
                    print "----> answers, thetaDash, theta, composedTheta, newGoalList"
                    print answers, thetaDash, theta, composedTheta, newGoalList
                    answers.update(self.infer(newGoalList, composedTheta))                    
                    print "priting ansers", answers
                else:
                    print 'passing here as unification could not be done'
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
            @param: expr is a string
                    thetaDict is a dict
            returns the subtituted expression
        """
        
        for variable, constant in thetaDict.iteritems():
            if variable in expr:    #this should be refined as it is very crude right now
                expr = expr.replace(variable, constant)
        return expr
    
    
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
        
        for item in argumentList:
            
            if (self.isVariable(item) and self.isVariable(constantList[counter])):
                unifierDict[item] = item #replace one variable by another
            elif (not self.isVariable(item) and self.isVariable(constantList[counter])):
                unifierDict[constantList[counter]] = item
            elif (self.isVariable(item) and  not self.isVariable(constantList[counter])):
                unifierDict[item] = constantList[counter]
            elif (item == constantList[counter]):
                pass
            else:   #in this case both are constants and hence cant be unified
                return 'False'
            counter += 1
        # print "True inside the unifier"
        # print unifierDict
        return unifierDict
    
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

    
if __name__ == "__main__":
    kb_obj = kb()
    final = kb_obj.infer(["H(John)"], {})
    print "printing final"
    print final