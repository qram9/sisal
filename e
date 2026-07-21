Graph {
----NODES----
__1 0 %na=MAIN ,Compound_of(PROCEDURE)
  Graph {
  ----NODES----
  __1 0 %na=IF_INTEGRAL;  ,Compound_of(IF)
    Graph {
    ----NODES----
    __7 SELECT [|6,4,2|] [|8|] %na=SELECT_0
    __6 0 %na=PREDICATE ,Compound_of(PREDICATE)
      Graph {
      ----NODES----
      __1 LESSER [|0,0|] [|2|]
      BOUNDARY [[(0,1,E,1);(0,0,I,0)], []]
      ----EDGES----
      __1:0 -> __0:0 [ID:1 BOOLEAN]
      __0:1 -> __1:1 [ID:6 INTEGRAL]
      __0:0 -> __1:0 [ID:6 INTEGRAL]
      GLOBAL-SYM: 
      FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
      INTEGRAL; I; (__0 : 0)
      INTEGRAL; E; (__0 : 1)
      LOCAL-SYM: 
      INTEGRAL; I; (__0 : 0)
      INTEGRAL; E; (__0 : 1)
      } 3
    __4 0 Compound_of(THEN) ,%na=THEN
      Graph {
      ----NODES----
      __2 TIMES [|0,1|] [|3|]
      __1 "2"
      BOUNDARY [[(0,0,I,0)], []]
      ----EDGES----
      __2:0 -> __0:0 [ID:6 INTEGRAL]
      __1:0 -> __2:1 [ID:6 INTEGRAL]
      __0:0 -> __2:0 [ID:6 INTEGRAL]
      GLOBAL-SYM: 
      FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
      INTEGRAL; I; (__0 : 0)
      INTEGRAL; E; (__0 : 1)
      LOCAL-SYM: 
      INTEGRAL; I; (__0 : 0)
      } 4
    __2 0 Compound_of(ELSE) ,%na=ELSE
      Graph {
      ----NODES----
      __7 SELECT [|6,4,2|] [|8|] %na=SELECT_0
      __6 0 %na=PREDICATE ,Compound_of(PREDICATE)
        Graph {
        ----NODES----
        __1 EQUAL [|0,0|] [|2|]
        BOUNDARY [[(0,1,E,1);(0,0,I,0)], []]
        ----EDGES----
        __1:0 -> __0:0 [ID:1 BOOLEAN]
        __0:1 -> __1:1 [ID:6 INTEGRAL]
        __0:0 -> __1:0 [ID:6 INTEGRAL]
        GLOBAL-SYM: 
        FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
        INTEGRAL; I; (__0 : 0)
        INTEGRAL; E; (__0 : 1)
        LOCAL-SYM: 
        INTEGRAL; I; (__0 : 0)
        INTEGRAL; E; (__0 : 1)
        } 3
      __4 0 Compound_of(THEN) ,%na=THEN
        Graph {
        ----NODES----
        __2 ADD [|0,1|] [|3|]
        __1 "3"
        BOUNDARY [[(0,1,E,0)], []]
        ----EDGES----
        __2:0 -> __0:0 [ID:6 INTEGRAL]
        __1:0 -> __2:1 [ID:6 INTEGRAL]
        __0:0 -> __2:0 [ID:6 INTEGRAL]
        GLOBAL-SYM: 
        FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
        INTEGRAL; I; (__0 : 0)
        INTEGRAL; E; (__0 : 1)
        LOCAL-SYM: 
        INTEGRAL; E; (__0 : 0)
        } 4
      __2 0 Compound_of(ELSE) ,%na=ELSE
        Graph {
        ----NODES----
        __2 SUBTRACT [|0,1|] [|3|]
        __1 "2"
        BOUNDARY [[(0,0,I,0)], []]
        ----EDGES----
        __2:0 -> __0:0 [ID:6 INTEGRAL]
        __1:0 -> __2:1 [ID:6 INTEGRAL]
        __0:0 -> __2:0 [ID:6 INTEGRAL]
        GLOBAL-SYM: 
        FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
        INTEGRAL; I; (__0 : 0)
        INTEGRAL; E; (__0 : 1)
        LOCAL-SYM: 
        INTEGRAL; I; (__0 : 0)
        } 4
      __1 0 %na=PREDICATE ,Compound_of(PREDICATE)
        Graph {
        ----NODES----
        __1 EQUAL [|0,0|] [|2|]
        BOUNDARY [[(0,1,E,1);(0,0,I,0)], []]
        ----EDGES----
        __1:0 -> __0:0 [ID:1 BOOLEAN]
        __0:1 -> __1:1 [ID:6 INTEGRAL]
        __0:0 -> __1:0 [ID:6 INTEGRAL]
        GLOBAL-SYM: 
        FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
        INTEGRAL; I; (__0 : 0)
        INTEGRAL; E; (__0 : 1)
        LOCAL-SYM: 
        INTEGRAL; I; (__0 : 0)
        INTEGRAL; E; (__0 : 1)
        } 3
      BOUNDARY [[(0,1,E,1);(0,0,I,0)], []]
      ----EDGES----
      __7:0 -> __0:0 [ID:6 INTEGRAL]
      __6:0 -> __7:0 [ID:1 BOOLEAN]
      __4:0 -> __7:1 [ID:6 INTEGRAL]
      __2:0 -> __7:2 [ID:6 INTEGRAL]
      __0:1 -> __4:0 [ID:6 INTEGRAL]
      __0:0 -> __2:0 [ID:6 INTEGRAL]
      __0:1 -> __1:1 [ID:6 INTEGRAL]
      __0:0 -> __1:0 [ID:6 INTEGRAL]
      GLOBAL-SYM: 
      FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
      INTEGRAL; I; (__0 : 0)
      INTEGRAL; E; (__0 : 1)
      LOCAL-SYM: 
      INTEGRAL; I; (__0 : 0)
      INTEGRAL; E; (__0 : 1)
      } 9
    __1 0 %na=PREDICATE ,Compound_of(PREDICATE)
      Graph {
      ----NODES----
      __1 LESSER [|0,0|] [|2|]
      BOUNDARY [[(0,1,E,1);(0,0,I,0)], []]
      ----EDGES----
      __1:0 -> __0:0 [ID:1 BOOLEAN]
      __0:1 -> __1:1 [ID:6 INTEGRAL]
      __0:0 -> __1:0 [ID:6 INTEGRAL]
      GLOBAL-SYM: 
      FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
      INTEGRAL; I; (__0 : 0)
      INTEGRAL; E; (__0 : 1)
      LOCAL-SYM: 
      INTEGRAL; I; (__0 : 0)
      INTEGRAL; E; (__0 : 1)
      } 3
    BOUNDARY [[(0,1,E,1);(0,0,I,0)], []]
    ----EDGES----
    __7:0 -> __0:0 [ID:6 INTEGRAL]
    __6:0 -> __7:0 [ID:1 BOOLEAN]
    __4:0 -> __7:1 [ID:6 INTEGRAL]
    __2:0 -> __7:2 [ID:6 INTEGRAL]
    __0:0 -> __4:0 [ID:6 INTEGRAL]
    __0:1 -> __2:1 [ID:6 INTEGRAL]
    __0:0 -> __2:0 [ID:6 INTEGRAL]
    __0:1 -> __1:1 [ID:6 INTEGRAL]
    __0:0 -> __1:0 [ID:6 INTEGRAL]
    GLOBAL-SYM: 
    FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
    INTEGRAL; I; (__0 : 0)
    INTEGRAL; E; (__0 : 1)
    LOCAL-SYM: 
    INTEGRAL; I; (__0 : 0)
    INTEGRAL; E; (__0 : 1)
    } 9
  BOUNDARY [[(0,1,E,1);(0,0,I,0)], [], %na=MAIN]
  ----EDGES----
  __1:0 -> __0:0 [ID:6 INTEGRAL]
  __0:1 -> __1:1 [ID:6 INTEGRAL]
  __0:0 -> __1:0 [ID:6 INTEGRAL]
  GLOBAL-SYM: 
  FUNCTION MAIN (INTEGRAL, INTEGRAL) RETURNS (INTEGRAL); MAIN; (__0 : 0)
  LOCAL-SYM: 
  INTEGRAL; I; (__0 : 0)
  INTEGRAL; E; (__0 : 1)
  } 4
BOUNDARY [[], []]
} 2
