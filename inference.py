#!/usr/bin/env python

import re
import copy

class kb(object):
    def __init__(self, initialKb = []):
        self.facts = {
        'B' : ["(John,Alice)", "(John,Bob)"],
        'D' : ["(John,Alice)", "(John,Bob)"],
        'R' : ["(Tom)"],
        'Q' : ["(Bob)"],
        }
            
        self.clauses = {
        'H' : [('x', 'A(x)'), ('x', 'R(x)'), ('x', 'G(x)')],
        '~H' : [('y', 'D(x,y)')],
        'A' : [('x', 'B(x,y) ^ C(x,y)')],
        'C' : [('x,y', 'D(x,y) ^ Q(y)')],
        'G' : [('x','F(x)')],
        'F' : [('x','H(x)')],
        }
        
        self.regex = re.compile('(\w+)\((.*?)\)')   #hard coding the values here
        self.visitedClauses = []
    
    def infer(self, quest, conjunctUnificationRes ={}):
        
        
        print "this is quest and conjunctUnificationRes", quest, conjunctUnificationRes
        
        #lhsRegex = re.compile('(\w+)(.*)')
        m = re.match(self.regex, quest)
        predicate = m.group(1)
        predArgs = m.group(2)
        
        print '************** predargs'
        print predArgs
        
        constant = predArgs.split(",") #[x.strip for x in predArgs.split(",")]
        
        #looking for the predicate in the facts to see if it is available        
        if predicate in self.facts:
            #checking whether unification is complete
            #this check needs to be fixed right now
            if self.isVariableInQuestArgs(constant): 
                #need to ensure that the arguments matches the finc signature
                for choice in self.generateSub(constant, predicate):
                    print "printing the generate stuff", choice
                    conjunctUnificationRes.update(choice)
                    print "returning true afte unifictaion and the theta valus is", conjunctUnificationRes
                    return True
                
                
            else:
                for fact in self.facts[predicate]:
                    print 'printing facts', fact
                    if predArgs in fact:
                        print "returning true after finding the quest in facts"
                        return True
                    else:
                        return False
        
        #checking if predicate is a part of the clause
        if not predicate in self.clauses:
            print "Cant be proved as there are no predcate in clauses"
            return "False"
        
        
        print "printig all predicates"
        print  self.clauses[predicate]
        
        
        for lhs in self.clauses[predicate]:        
            
            print "prinitng lhs"
            print lhs
            
            arguments =  lhs[0].split(',')
            
            print "atguments and constants"
            print arguments, constant
            unificatonRes = self.unify(arguments, constant)
            print "unification result", unificatonRes
    
            
            if unificatonRes:
                conjunctUnificationRes = copy.deepcopy(unificatonRes)
                conjunctiveClauses = [x.strip() for x in lhs[1].split("^")]
                
                print "the conjunctive clause"
                print conjunctiveClauses
                
                for clause in conjunctiveClauses:
                    
                    print "clause ----------->", clause 
                    unifiedClause = self.replaceWithTheta(clause, conjunctUnificationRes)
                    print "the unifiedClause and the status of theta now"
                    print unifiedClause, conjunctUnificationRes
                    
                    if not self.infer(unifiedClause, conjunctUnificationRes):
                        print "<<<<<<<<<<<<<<<<<<<<breaking here because the inference returned is false"
                        break
                                 
            return True
        return False
    
    def generateSub(self, queryArgsList, predicate):
        """
            Generator used to generate different values of theta whenever possible
            @param: queryArgsList -> the arguments of the query which has been unified so far
                    predicate -> predicate of the query
            returns a new theta dict everytime
        """
        
        factArgList = self.facts[predicate]
        
        for eachArgSet in factArgList:
            thetaDict = {}
            counter = 0
            removeParanRegex = re.compile('\((.*?)\)')
            m = re.search(removeParanRegex, eachArgSet)
            eachArgSet = m.group(1)
            eachArgList = eachArgSet.split(',')
            
            # print "------------------ > each queryarglist and eacharglist and eachargset"
            # print queryArgsList, eachArgList, eachArgSet
            
            for arg in queryArgsList:
                if self.isVariable(arg):
                    thetaDict[arg]= eachArgList[counter]
                else:
                    # print '^^^^^^^^^^^^^^^^^^^^^^^^'
                    # print arg, eachArgList[counter]
                    
                    if arg == eachArgList[counter]:
                        pass
                    else:
                        yield {}
    
                counter += 1
            # print '&&&&&&&&&&&& this has to be fixed'
            # print thetaDict
            yield thetaDict
    
    
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
            #print"true"
            return True
        else:
            #print "false"
            return False
    
    
    def unify(self, argumentList, constantList, unifierDict = {}):
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
        
        for item in argumentList:
            if (self.isVariable(item) and self.isVariable(constantList[counter])):
                unifierDict[item] = item #replace one variable by another
            elif (not self.isVariable(item) and self.isVariable(constantList[counter])):
                unifierDict[constantList[counter]] = item
            elif (self.isVariable(item) and  not self.isVariable(constantList[counter])):
                unifierDict[item] = constantList[counter]
            else:   #in this case both are constants and hence cant be unified
                print "false and cant be unified"
                return False
            counter += 1
        # print "True inside the unifier"
        # print unifierDict
        return unifierDict
    
if __name__ == "__main__":
    kb_obj = kb()
    final = kb_obj.infer("A(John)", {})
    print "printing final"
    print final