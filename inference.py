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
        
        
        #lhsRegex = re.compile('(\w+)(.*)')
        m = re.match(self.regex, quest)
        
        print "this is quest", quest
        print m
        
        predicate = m.group(1)
        predArgs = m.group(2)
        
        print predArgs
        
        constant = predArgs.split(",") #[x.strip for x in predArgs.split(",")]
        
        #looking for the predicate in the facts to see if it is available        
        if predicate in self.facts:
            for fact in self.facts[predicate]:
                print 'printing facts', fact
                if predArgs in fact:
                    print "True"
                    return "True"
        
        #checking if predicate is a  part of the clause
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
                    
                    #check if there are exra variables in the lhs of the implication when comapred to rhs
                    #if found then add them to theta so that it can be used by the generator
                    
                    m = re.match(self.regex, clause)
                    lhsPredicate = m.group(1)
                    lhsPredArgs = m.group(2)
                    lhsArgs = lhsPredArgs.split(",")
                    
                    for newArg in lhsArgs:      #adds new variable to the deep copy of the theta mapping
                        if not newArg in conjunctUnificationRes:
                            conjunctUnificationRes[newArg] = newArg
                    
                    
                    
                    print "check if partial unification is done and theta right now is", conjunctUnificationRes
                    print self.isVariableInTheta(conjunctUnificationRes)
                    #checking whether unification is complete
                    if self.isVariableInTheta(conjunctUnificationRes):
                        if lhsPredicate in self.facts:     #checking if the generator can be used
                            partiallyUnifiedArgList =  []        #unified list
                            for word in lhsArgs:
                                partiallyUnifiedArgList.append(conjunctUnificationRes.get(word,''))
                            
                            print "printing unified argumenst list"
                            print partiallyUnifiedArgList
                    
                            #need to ensure that the arguments matches the finc signature
                            for choice in self.generateSub(partiallyUnifiedArgList, lhsPredicate):
                                conjunctUnificationRes.update(choice)
                            
                                unifiedClause = self.replaceWithTheta(clause, conjunctUnificationRes)
                        
                                print 'unified clause ****************'
                                print unifiedClause 
                                if not self.infer(unifiedClause, conjunctUnificationRes):
                                    break
                                
                                

                    else:
                        unifiedClause = self.replaceWithTheta(clause, conjunctUnificationRes)
                        if not self.infer(unifiedClause, conjunctUnificationRes):
                            break            #     break 
                                
            return True
        return False
    
    
    
    
    
    
# print '**************'
# print self.visitedClauses
# 
# if unifiedClause not in self.visitedClauses:
#     self.visitedClauses.append(unifiedClause)
# else:
#     print "loop found"
#     self.visitedClauses = []

    
    
    def generateSub(self, queryArgsList, predicate):
        
        factArgList = self.facts[predicate]
        for eachArgSet in factArgList:
            thetaDict = {}
            counter = 0
            removeParanRegex = re.compile('\((.*?)\)')
            m = re.search(removeParanRegex, eachArgSet)
            eachArgSet = m.group(1)
            factArgList = eachArgSet.split(',')
            
            for arg in queryArgsList:
                if self.isVariable(arg):
                    thetaDict[arg]= factArgList[counter]
                else:
                    if arg == factArgList[counter]:
                        pass
                    else:
                        yield {}
    
                counter += 1
            yield thetaDict
    
    
    def isVariableInTheta(self, theta):
        for k, v in theta.iteritems():
            if self.isVariable(v):
                return True
        return False
    
    
    def replaceWithTheta(self, expr, thetaDict):
        
        for variable, constant in thetaDict.iteritems():
            if variable in expr:    #this should be refined as it is very crude right now
                expr = expr.replace(variable, constant)
        return expr
    
    
    def isVariable(self, string):
        regex = re.compile("^[a-z]")
        m = re.match(regex, string)
        
        if m:
            #print"true"
            return True
        else:
            #print "false"
            return False
    
    
    def unify(self, s1List, s2List, unifierDict = {}):
        #need to standerdize here before unification      
        counter = 0
        
        for item in s1List:
            if (self.isVariable(item) and self.isVariable(s2List[counter])):
                unifierDict[item] = s2List[counter] #replace one variable by another
            elif (not self.isVariable(item) and self.isVariable(s2List[counter])):
                unifierDict[s2List[counter]] = item
            elif (self.isVariable(item) and  not self.isVariable(s2List[counter])):
                unifierDict[item] = s2List[counter]
            else:   #in this case both are constants and hence cant be unified
                print "false and cant be unified"
                return False
            counter += 1
        print "True inside the unifier"
        print unifierDict
        return unifierDict
    
if __name__ == "__main__":
    kb_obj = kb()
    final = kb_obj.infer("A(John)", {})
    print "printing final"
    print final