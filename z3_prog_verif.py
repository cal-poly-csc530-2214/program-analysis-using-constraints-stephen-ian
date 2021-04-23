from staticfg import CFGBuilder
import z3
import re

class Code:
  def __init__(self, src):
      print('s')
    
class Assignment(Code):
  def __init__(self, var, val):
    self.var = var
    self.val = val.strip()

  def __repr__(self):
    return "{} = {}".format(self.var, self.val)

class Loop(Code):
  def __init__(self, src, cond):
    self.src = src
    self.cond = cond
    
  def __repr__(self):
    return src

class Condition(Code):
  def __init__(self, var, op, val):
    self.var = var
    self.op = op
    self.val = val
    
  def __repr__(self):
    return "{} {} {}".format(self.var, self.op, self.val)

def defStrToObject(defStr):
  var = defStr[0]
  op = defStr[2]
  if op == "=":
    return Assignment(var, defStr[3:])
  elif op == "+":
    return Assignment(var, "{} + {}".format(var, defStr[5:]))
    

# converts things of form "x > 0" to conditional object
def condStrToObject(condStr):
  var = condStr[0]
  op = condStr[2]
  if condStr[3] == "=":
    op = op + "="
    val = condStr[4:].strip()
    return Condition(var, op, val)
  else:
    val = condStr[3:].strip()
    return Condition(var, op, val) 
  
  
  

def loopStrToObject(loopStr):
  if loopStr[0] == "w":
    return Loop(loopStr, condStrToObject(loopStr[6:].strip()))
    
"""
  Return dictionary of K:ID to V:code fragment
"""
def getCodeDef(graph):
    cDict = {}
    for node in graph:
        nnode = node
        # Finds all code definitions
        reLi = re.findall("[^>][\s]\d \[label", nnode)
        if reLi:
            cId = int(nnode.strip().split(" ")[0])
            cFrag = nnode.strip().split("\"")[1].split("\n")
            cFrag.remove('')
            cDict[cId] = cFrag
    return cDict

"""
    Return dictionary of K:tuple(source, target) to V:condition
"""
def getConditions(graph):
    # Get Cutset
    condDict = {}
    for node in graph:
        reLi = re.findall("\d -> \d", node)
        if reLi:
            arr = reLi[0].split("->")
            stTuple = (int(arr[0]),int(arr[1]))
            condDict[stTuple] = re.findall("\"[^\"]*\"", node)[0].split("\"")[1]
    return condDict


cfg = CFGBuilder().build_from_file('z3_test.py', './z3_test.py')

graph = cfg._build_visual()
# graph.render('z3_graph.gv', view=True)  
# print(graph.graph_attr)

# first pass - save nodes with location
# second pass - find back-edges and put cut points at locations

# Get Code Frag definitions
cDict = getCodeDef(graph)
print(cDict)

# Get condition statements parsed
condDict = getConditions(graph)
cutSet = set()

# Find cutset
for source, target in condDict.keys():
  if source > target:
    cutSet.add(target)

# Get fragments going to set and going out of set
# for cut_point in cutSet:
conditionsLi = []
for source, target in condDict.keys():
  stTuple = (source, target)
  # print(stTuple, condDict[stTuple])
  if source in cutSet: # Going from cutset to node (postcondition or loop)
    if (target, source) in condDict.keys(): # LOOP CONDITION
      """
      loop-condition: 4->5
      5 = ['x = x + y', 'y += 1']
      - while x < 0 == I AND x < 0
          - I AND x < 0 => I[(y+=1)/y, (x+y)/x]
          - 4 INVARIANT => INVARIANT ( ASSIGNMENT )
      """
      loopCond = condStrToObject(condDict[stTuple])
      lhStr = "I AND {0} {1} {2} => ".format(
        loopCond.var, 
        loopCond.op, 
        loopCond.val)
      lAssign = [defStrToObject(assign) for assign in cDict[target]]
      rhStr = "I[ "
      for la in lAssign:
        rhStr = rhStr + " ({0})/{1},".format(la.val, la.var)
      rhStr = rhStr[:-1] # remove comma
      rhStr = rhStr + " ]" # append bracket
      conditionsLi.append(lhStr + rhStr)
    else: # POSTCONDITION
      """
      post-condition: 4->6
      6 = ['assert y > 0']
      - I AND x >= 0 => y > 0
      - 4 INVARIANT => 6
      """
      # stupid code to remove paran
      tempStr = condDict[stTuple].split("(")[1].split(")")[0]
      lec = condStrToObject(tempStr)
      lhStr = "I AND {0} {1} {2} => ".format(lec.var, lec.op, lec.val)
      rhStr = ""
      if 'assert' in cDict[target][0]:
        rhStr = cDict[target][0].split("assert")[1]
      else:
        rhStr = cDict[target][0]
      conditionsLi.append(lhStr + rhStr)
  elif target in cutSet: # From node to cutset (precondition)
    if not ((target, source) in condDict.keys()): # no loops
      """
      3 = [x = -50]
      4 = [while x < 0]
      - true => I[-50/x] because x=-50 and x is in 4
      - TRUE => 4 INVARIANT ( ASSIGNMENT)
      """
      convObj = defStrToObject(cDict[source][0]) # TODO: change to allow multiple while vars.
      if type(convObj).__name__ == 'Assignment':
        if convObj.var in cDict[target][0]: # VARIABLE is in INVARIANT
          conditionsLi.append("true => I[ {0}/{1} ]".format(convObj.val, convObj.var))
    
print(conditionsLi)



"""
pre-condition: 3->4
3 = [x = -50]
4 = [while x < 0]
- true => I[-50/x] because x=-50 and x is in 4
- TRUE => 4 INVARIANT ( ASSIGNMENT)

loop-condition: 4->5
5 = ['x = x + y', 'y += 1']
- while x < 0 == I AND x < 0
    - I AND x < 0 => I[(y+=1)/y, (x+y)/x]
    - 4 INVARIANT => INVARIANT ( ASSIGNMENT )

post-condition: 4->6
6 = ['assert y > 0']
- I AND x >= 0 => y > 0
- 4 INVARIANT => 6



template : (a1x + a2y + a3 >= 0 \/ a4x + a5y + a6 >= 0)
"""

