---- MODULE RAFT_3_3 ----
EXTENDS raft_alt, TLC

\* CONSTANT definitions @modelParameterConstants:0Follower
const_168061104927626000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:1Leader
const_168061104927727000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:2LargestTerm
const_168061104927728000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:3Nil
const_168061104927729000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:4MaxLogIndex
const_168061104927730000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:5Candidate
const_168061104927731000 == 
"candidate"
----

\* CONSTANT definitions @modelParameterConstants:6MaxValue
const_168061104927732000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:7Server
const_168061104927733000 == 
{1,2,3}
----

=============================================================================
\* Modification History
