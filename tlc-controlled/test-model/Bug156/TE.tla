---- MODULE TE ----
EXTENDS FindOpWithoutPrint, TLC

\* TRACE EXPLORER variable declaration @traceExploreExpressions
VARIABLES __trace_var_130942095004115000
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions
trace_def_130942095003114000 ==
<<delim, leftTok>>
----

\* TRACE INIT definitiontraceExploreInit
init_130942095005116000 ==
 pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
defaultInitValue
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_77"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<>>
)/\
 tempVar1 = (
defaultInitValue
)/\
 tempVar2 = (
defaultInitValue
)/\
 tempVar3 = (
defaultInitValue
)
----

\* TRACE NEXT definitiontraceExploreNext
next_130942095006117000 ==
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
defaultInitValue
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_77"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<>>
)/\
 tempVar1 = (
defaultInitValue
)/\
 tempVar2 = (
defaultInitValue
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
defaultInitValue
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_78"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<>>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
defaultInitValue
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_78"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<>>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
defaultInitValue
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_31"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
defaultInitValue
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_31"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
defaultInitValue
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_33"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
defaultInitValue
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_33"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
defaultInitValue
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_36"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
defaultInitValue
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_36"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
defaultInitValue
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_38"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
defaultInitValue
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_38"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[null |-> "null"]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_39"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[null |-> "null"]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_39"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
10
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
10
)/\
 returnVal' = (
[null |-> "null"]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_5"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
10
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_40", token |-> <<>>, pos_f |-> defaultInitValue, left_ |-> defaultInitValue, rt_ |-> defaultInitValue, procedure |-> "findMaximalIdCharSeq"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
10
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
10
)/\
 returnVal = (
[null |-> "null"]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_5"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
10
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_40", token |-> <<>>, pos_f |-> defaultInitValue, left_ |-> defaultInitValue, rt_ |-> defaultInitValue, procedure |-> "findMaximalIdCharSeq"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
10
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
10
)/\
 returnVal' = (
[null |-> "null"]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_6"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
10
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_40", token |-> <<>>, pos_f |-> defaultInitValue, left_ |-> defaultInitValue, rt_ |-> defaultInitValue, procedure |-> "findMaximalIdCharSeq"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
10
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
10
)/\
 returnVal = (
[null |-> "null"]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_6"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
10
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_40", token |-> <<>>, pos_f |-> defaultInitValue, left_ |-> defaultInitValue, rt_ |-> defaultInitValue, procedure |-> "findMaximalIdCharSeq"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
10
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
10
)/\
 returnVal' = (
[null |-> "null"]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_6"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
11
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_40", token |-> <<>>, pos_f |-> defaultInitValue, left_ |-> defaultInitValue, rt_ |-> defaultInitValue, procedure |-> "findMaximalIdCharSeq"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
10
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
10
)/\
 returnVal = (
[null |-> "null"]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_6"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
11
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_40", token |-> <<>>, pos_f |-> defaultInitValue, left_ |-> defaultInitValue, rt_ |-> defaultInitValue, procedure |-> "findMaximalIdCharSeq"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_40"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_40"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_43"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_43"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_46"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_46"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_47"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_47"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_62"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_62"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_63"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_63"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_29"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [pc |-> "Lbl_64", procedure |-> "skipLeftOverSpaces"],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_29"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [pc |-> "Lbl_64", procedure |-> "skipLeftOverSpaces"],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_64"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_64"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_63"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
FALSE
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_63"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
FALSE
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_69"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
FALSE
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
10
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_69"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
FALSE
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
10
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_70"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_70"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_30"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [pc |-> "Lbl_71", procedure |-> "skipRightOverSpaces"],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_30"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [pc |-> "Lbl_71", procedure |-> "skipRightOverSpaces"],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_71"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
defaultInitValue
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_71"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
defaultInitValue
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_17"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<<[pc |-> "Lbl_72", pos_find |-> defaultInitValue, procedure |-> "findMatchingRightParen"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_17"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<<[pc |-> "Lbl_72", pos_find |-> defaultInitValue, procedure |-> "findMatchingRightParen"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_18"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<<[pc |-> "Lbl_72", pos_find |-> defaultInitValue, procedure |-> "findMatchingRightParen"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_18"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<<[pc |-> "Lbl_72", pos_find |-> defaultInitValue, procedure |-> "findMatchingRightParen"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_19"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
11
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_19"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
11
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_20"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
12
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_20"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
12
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_21"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
12
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_21"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
12
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_22"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
0
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_22"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
0
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_26"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
0
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_26"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
0
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_22"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
1
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_22"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
1
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_26"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
1
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_26"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
1
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_22"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
2
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_22"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
2
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_26"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
2
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_26"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
2
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_22"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
3
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_22"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
3
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_26"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
3
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_26"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
3
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_22"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
4
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_22"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
4
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
0
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
11
)/\
 pc' = (
"Lbl_20"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
1
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
13
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
4
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
0
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
11
)/\
 pc = (
"Lbl_20"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
1
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
13
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
4
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_72",
     pos |-> defaultInitValue,
     delim |-> defaultInitValue,
     ipos |-> defaultInitValue,
     jdelim |-> defaultInitValue,
     delimLen |-> defaultInitValue,
     procedure |-> "findMatchingRightInner" ],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
14
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_72"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
14
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_72"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
14
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_30"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
14
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [pc |-> "Lbl_73", procedure |-> "skipRightOverSpaces"],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
14
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_30"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
14
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [pc |-> "Lbl_73", procedure |-> "skipRightOverSpaces"],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
14
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_30"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
15
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [pc |-> "Lbl_73", procedure |-> "skipRightOverSpaces"],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
14
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_30"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
15
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [pc |-> "Lbl_73", procedure |-> "skipRightOverSpaces"],
   [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
14
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_73"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
TRUE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
15
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
14
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_73"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
TRUE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
15
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
14
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_70"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
FALSE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
15
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
14
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_70"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
FALSE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
15
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
14
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
FALSE
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_76"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
FALSE
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
11
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
10
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
15
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
14
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
FALSE
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_76"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
FALSE
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
11
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
10
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
15
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
[token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11]
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_79"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
15
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<>>
)/\
 tempVar1' = (
(-1 :> "")
)/\
 tempVar2' = (
10
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_79"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
15
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<>>
)/\
 tempVar1 = (
(-1 :> "")
)/\
 tempVar2 = (
10
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_78"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
15
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 10, rightPos |-> 11])
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_78"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
15
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_31"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_31"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_33"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_33"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_36"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
defaultInitValue
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
defaultInitValue
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_36"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
defaultInitValue
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
defaultInitValue
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<< [ pc |-> "Lbl_79",
     currentToken |-> defaultInitValue,
     left |-> defaultInitValue,
     rt |-> defaultInitValue,
     notDone |-> defaultInitValue,
     foundBangToken |-> defaultInitValue,
     temp1 |-> defaultInitValue,
     temp2 |-> defaultInitValue,
     temp3 |-> defaultInitValue,
     procedure |-> "findTokenSpecs" ] >>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
defaultInitValue
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_1"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
defaultInitValue
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_1"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
0
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
defaultInitValue
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
0
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
defaultInitValue
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
0
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
0
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
0
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_4"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
0
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_4"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
0
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
0
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
1
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
1
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
1
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
1
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
2
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
2
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
2
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
2
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
3
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
3
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
3
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
3
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
4
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
4
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
4
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
4
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
5
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
5
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
5
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
5
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
5
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_4"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
5
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_4"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
5
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
5
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
6
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
6
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
6
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
6
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
6
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_4"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
6
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_4"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
6
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
6
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
7
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
7
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
7
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
7
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
7
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_4"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
7
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_4"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
7
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
7
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
8
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
8
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
8
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
8
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
8
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_4"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
0
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
8
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_4"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
0
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
8
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
8
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
9
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
9
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
9
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
9
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
10
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
10
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
10
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
10
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
11
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
11
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
11
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
11
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
12
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
12
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
12
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
12
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
13
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
13
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
13
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
13
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
14
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
14
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
14
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
14
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
15
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
15
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
15
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
15
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
16
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
16
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
16
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
16
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
17
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
17
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
17
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
17
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
18
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
18
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
18
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
18
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
19
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
19
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
19
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
19
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
20
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
20
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
20
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
20
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
21
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
21
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
21
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
21
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
22
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
22
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
22
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
22
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
23
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
23
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
23
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
23
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
24
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
24
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
24
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
24
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
25
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
25
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
25
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
25
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
26
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
26
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
26
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
26
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
27
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
27
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
27
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
27
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
28
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
28
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
28
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
28
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
29
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
29
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
29
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
29
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
30
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
30
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
30
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
30
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
31
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
31
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
31
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
31
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
32
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
32
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
32
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
32
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
33
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
33
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
33
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
33
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
34
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
34
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
34
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
34
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
35
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
35
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
35
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
35
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
36
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
36
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
36
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
36
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
37
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
37
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
37
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
37
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
38
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
38
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
38
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
38
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
39
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
39
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
39
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
39
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
40
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
40
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
40
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
40
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
41
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
41
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
41
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
41
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
42
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
42
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
42
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
42
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_3"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
43
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_2"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
 delim_' = (
defaultInitValue
)/\
 tokArray' = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken' = (
FALSE
)/\
 currentToken' = (
defaultInitValue
)/\
 stack' = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2' = (
11
)/\
 tempVar3' = (
defaultInitValue
))
\/
( pos_f = (
defaultInitValue
)/\
 foundTokenSpecs = (
<<>>
)/\
 delim = (
defaultInitValue
)/\
 leftTok = (
defaultInitValue
)/\
 left_ = (
defaultInitValue
)/\
 returnVal = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_ = (
defaultInitValue
)/\
 line = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_ = (
defaultInitValue
)/\
 i = (
43
)/\
 foundBangToken = (
defaultInitValue
)/\
 pos = (
defaultInitValue
)/\
 pc = (
"Lbl_2"
)/\
 ipos_ = (
defaultInitValue
)/\
 pos_fi = (
defaultInitValue
)/\
 pos_fin = (
defaultInitValue
)/\
 notDone = (
defaultInitValue
)/\
 pos_find = (
11
)/\
 temp1 = (
defaultInitValue
)/\
 temp2 = (
defaultInitValue
)/\
 temp3 = (
defaultInitValue
)/\
 delimLen = (
defaultInitValue
)/\
 rt = (
defaultInitValue
)/\
 notLastToken = (
FALSE
)/\
 ipos = (
defaultInitValue
)/\
 left = (
defaultInitValue
)/\
 token = (
<<>>
)/\
 rt_ = (
defaultInitValue
)/\
 rightTok = (
defaultInitValue
)/\
 jdelim = (
defaultInitValue
)/\
 tokIdx = (
-1
)/\
 pos_ = (
11
)/\
 curPos = (
11
)/\
 delim_ = (
defaultInitValue
)/\
 tokArray = (
( 0 :> (0 :> "(" @@ 1 :> "+" @@ 2 :> ")") @@
  1 :> (0 :> "-" @@ 1 :> "+" @@ 2 :> "-" @@ 3 :> ">") @@
  2 :> (0 :> "<" @@ 1 :> "=" @@ 2 :> ">") @@
  3 :> (0 :> "." @@ 1 :> "." @@ 2 :> ".") @@
  4 :> (0 :> ":" @@ 1 :> ":" @@ 2 :> "=") @@
  5 :> (0 :> "(" @@ 1 :> "-" @@ 2 :> ")") @@
  6 :> (0 :> "(" @@ 1 :> "." @@ 2 :> ")") @@
  7 :> (0 :> "(" @@ 1 :> "/" @@ 2 :> ")") @@
  8 :> (0 :> "(" @@ 1 :> "\\" @@ 2 :> "X" @@ 3 :> ")") @@
  9 :> (0 :> "-" @@ 1 :> "-") @@
  10 :> (0 :> "*" @@ 1 :> "*") @@
  11 :> (0 :> "+" @@ 1 :> "+") @@
  12 :> (0 :> "<" @@ 1 :> ":") @@
  13 :> (0 :> "<" @@ 1 :> "=") @@
  14 :> (0 :> "<" @@ 1 :> " ") @@
  15 :> (0 :> ">" @@ 1 :> "=") @@
  16 :> (0 :> "." @@ 1 :> ".") @@
  17 :> (0 :> "|" @@ 1 :> "|") @@
  18 :> (0 :> "[" @@ 1 :> "]") @@
  19 :> (0 :> "<" @@ 1 :> ">") @@
  20 :> (0 :> "/" @@ 1 :> "\\") @@
  21 :> (0 :> "\\" @@ 1 :> "/") @@
  22 :> (0 :> "/" @@ 1 :> "/") @@
  23 :> (0 :> "/" @@ 1 :> "=") @@
  24 :> (0 :> "~" @@ 1 :> ">") @@
  25 :> (0 :> "=" @@ 1 :> ">") @@
  26 :> (0 :> "=" @@ 1 :> "<") @@
  27 :> (0 :> "=" @@ 1 :> "|") @@
  28 :> (0 :> "^" @@ 1 :> "^") @@
  29 :> (0 :> "#" @@ 1 :> "#") @@
  30 :> (0 :> "|" @@ 1 :> "-") @@
  31 :> (0 :> "|" @@ 1 :> "=") @@
  32 :> (0 :> "&" @@ 1 :> "&") @@
  33 :> (0 :> "$" @@ 1 :> "$") @@
  34 :> (0 :> "?" @@ 1 :> "?") @@
  35 :> (0 :> "%" @@ 1 :> "%") @@
  36 :> (0 :> "@" @@ 1 :> "@") @@
  37 :> (0 :> "!" @@ 1 :> "!") @@
  38 :> (0 :> ":" @@ 1 :> ">") @@
  39 :> (0 :> ":" @@ 1 :> "=") @@
  40 :> (0 :> "^" @@ 1 :> "+") @@
  41 :> (0 :> "^" @@ 1 :> "*") @@
  42 :> (0 :> "^" @@ 1 :> "#") @@
  43 :> (0 :> "~") @@
  44 :> (0 :> "=") @@
  45 :> (0 :> "#") @@
  46 :> (0 :> "^") @@
  47 :> (0 :> "-") @@
  48 :> (0 :> "*") @@
  49 :> (0 :> ">") @@
  50 :> (0 :> "<") @@
  51 :> (0 :> "+") @@
  52 :> (0 :> "|") @@
  53 :> (0 :> "&") @@
  54 :> (0 :> "$") @@
  55 :> (0 :> "%") @@
  56 :> (0 :> "\\") @@
  57 :> (0 :> "'") )
)/\
 lastToken = (
FALSE
)/\
 currentToken = (
defaultInitValue
)/\
 stack = (
<<[pc |-> "Lbl_37", i |-> defaultInitValue, pos_ |-> defaultInitValue, tokArray |-> defaultInitValue, tokIdx |-> defaultInitValue, procedure |-> "findTokenIn"], [pc |-> "Lbl_79", currentToken |-> defaultInitValue, left |-> defaultInitValue, rt |-> defaultInitValue, notDone |-> defaultInitValue, foundBangToken |-> defaultInitValue, temp1 |-> defaultInitValue, temp2 |-> defaultInitValue, temp3 |-> defaultInitValue, procedure |-> "findTokenSpecs"]>>
)/\
 tempVar1 = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 tempVar2 = (
11
)/\
 tempVar3 = (
defaultInitValue
)/\
 pos_f' = (
defaultInitValue
)/\
 foundTokenSpecs' = (
<<>>
)/\
 delim' = (
defaultInitValue
)/\
 leftTok' = (
defaultInitValue
)/\
 left_' = (
defaultInitValue
)/\
 returnVal' = (
(0 :> [token |-> (0 :> "f"), leftPos |-> 0, rightPos |-> 1])
)/\
 delimLen_' = (
defaultInitValue
)/\
 line' = (
( 0 :> ";" @@
  1 :> ";" @@
  2 :> ";" @@
  3 :> ";" @@
  4 :> ";" @@
  5 :> ";" @@
  6 :> ";" @@
  7 :> ";" @@
  8 :> ";" @@
  9 :> ";" @@
  10 :> "f" @@
  11 :> "(" @@
  12 :> "b" @@
  13 :> ")" @@
  14 :> " " @@
  15 :> ";" @@
  16 :> ";" @@
  17 :> ";" @@
  18 :> ";" @@
  19 :> ";" @@
  20 :> ";" @@
  21 :> ";" @@
  22 :> ";" @@
  23 :> ";" @@
  24 :> ";" )
)/\
 jdelim_' = (
defaultInitValue
)/\
 i' = (
43
)/\
 foundBangToken' = (
defaultInitValue
)/\
 pos' = (
defaultInitValue
)/\
 pc' = (
"Lbl_3"
)/\
 ipos_' = (
defaultInitValue
)/\
 pos_fi' = (
defaultInitValue
)/\
 pos_fin' = (
defaultInitValue
)/\
 notDone' = (
defaultInitValue
)/\
 pos_find' = (
11
)/\
 temp1' = (
defaultInitValue
)/\
 temp2' = (
defaultInitValue
)/\
 temp3' = (
defaultInitValue
)/\
 delimLen' = (
defaultInitValue
)/\
 rt' = (
defaultInitValue
)/\
 notLastToken' = (
FALSE
)/\
 ipos' = (
defaultInitValue
)/\
 left' = (
defaultInitValue
)/\
 token' = (
<<>>
)/\
 rt_' = (
defaultInitValue
)/\
 rightTok' = (
defaultInitValue
)/\
 jdelim' = (
defaultInitValue
)/\
 tokIdx' = (
-1
)/\
 pos_' = (
11
)/\
 curPos' = (
11
)/\
)/\
)/\
0