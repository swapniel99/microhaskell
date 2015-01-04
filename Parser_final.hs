import Data.Char
import Data.List

type Fname = String
type Var = String

data Program = Prog [Fundef] Exp deriving (Show,Eq)
data Fundef = Fun String [String] Exp deriving (Show,Eq)
data Exp = I Int | B Bool | V String | Nil | Fname String | App Exp Exp deriving (Show,Eq)

type Parser symbol result = [symbol]->[([symbol],result)]

charToNum c = (fromInteger.read) [c]

symbol::Char->Parser Char Char
symbol c [] = []
symbol c (x:xs)| x==c = [(xs,c)] 
               | otherwise = []
                             
satisfy::(a->Bool)->Parser a a
satisfy p [] = []
satisfy p (x:xs) | p x = [(xs,x)]
                 | otherwise = []

succeed::a->Parser s a
succeed x l = [(l,x)]


token::Eq a=>[a]->Parser a [a]

token k xs |k==(take n xs) = [((drop n xs),k)]  
           |otherwise = []
            where n = length k

fail xs = []

epsilon = succeed ()

infixr 6 <*>,<*,*>
infixr 5 <@
infixr 4 <|>

(<*>)::Parser s a->Parser s b->Parser s (a,b)
(p1 <*> p2) xs = [(xs2,(v1,v2))|(xs1,v1)<-p1 xs,(xs2,v2)<-p2 xs1]


(<|>)::Parser s a->Parser s a->Parser s a
(p1 <|> p2) xs = p1 xs ++ p2 xs

(<@)::Parser s a -> (a->b)-> Parser s b
(p <@ f) xs = [(xs,f v)|(xs,v)<-p xs] 

(<*)::Parser s a->Parser s b->Parser s a 
p1 <* p2 = p1 <*> p2 <@ fst

(*>)::Parser s a->Parser s b->Parser s b
p1 *> p2 = p1 <*> p2 <@ snd

(<:*>)::Parser s a->Parser s [a]->Parser s [a]
p1 <:*> p2 = p1 <*> p2 <@ listify 

listify (x,xs) = x:xs

zeroOrMore::Parser s a->Parser s [a]
zeroOrMore p =  (p <:*> (zeroOrMore p)) <|> succeed [] 
               
oneOrMore::Parser s a->Parser s [a]
oneOrMore p = p <:*> (zeroOrMore p)

option::Parser s a->Parser s [a]
option p =   succeed [] <|> p <@ f  
            where f x = [x]

(<?@) ::Parser s [a]->(b,(a->b))->Parser s b
p <?@ (no,yes) = p <@ f
                 where f [] = no
                       f [x]= yes x

digit::Parser Char Char
digit = satisfy isDigit 
alpha = satisfy isAlpha 

number::Num a => [Char]->[([Char],a)]
number = ((oneOrMore digit) <@ (fromInteger.read))  

determ p xs | null l = []
            | otherwise = [head l]
                       where l = p xs

greedy = determ.zeroOrMore

sp  = greedy (symbol ' ')

pack s1 p s2 = s1 *> p <* s2

paranthesized p = pack (symbol '(') p (symbol ')')

fractional = oneOrMore digit <@ (foldr f 0.0)
             where f x y = (charToNum x + y)/10


float = (number <*> 
        (option (symbol '.' *> fractional) <?@ (0.0,id))) <@ uncurry (+)
               
listOf p s = p <:*> (zeroOrMore (s *> p)) <|> succeed []

commaList p = listOf p (symbol ',')

spsymbol c = symbol c <* sp
chainr p s = (zeroOrMore (p <*> s)) <*> p <@ uncurry (flip (foldr f))
             where f (x,op) y = x `op` y


chainl p s = p <*> (zeroOrMore (s <*> p)) <@ uncurry (foldl f) 
                    where f x (op,y) = x `op` y 

name = (alpha <:*> greedy (alpha <|> digit)) 

reservedWords = [ "if" , "else" , "null" , "car" , "cdr" , "then"]
identifier xs | l==[] = []
              | ((snd (head l)) `elem` reservedWords)=[] 
              | otherwise = l     
                where l = name xs                                         

---------------------Exp
boolean = (token "True") <@ const True  <|> (token "False") <@ const False  

sqrBracketed p = pack (symbol '[' <* sp)  p (sp *> symbol ']')
commasp = (symbol ',') <* sp
list::Parser Char Exp
list = sqrBracketed((listOf lterm commasp) <@ foldr (\x y-> App (App (Fname "cons") x) y) Nil)



headterm = headtoken *> factor <@ (App (Fname "car")) 
tailterm = tailtoken *> factor <@ (App (Fname "cdr"))

factor::Parser Char Exp
factor = (number <@ I)
         <|>
         (boolean <@ B)
         <|> headterm <|> tailterm
         <|>
         (identifier <@ (\x -> Fname x))
         <|>
         (identifier <@ V)
         <|>list
         <|>paranthesized expr
appterm = chainl (sp *> factor) ((symbol ' ') <@ const (\x y -> App x y))
         

sptoken t = determ (sp *> (token t) <* sp)
headtoken = sptoken "car "
tailtoken = sptoken "cdr "
iftoken = sptoken "if "
thentoken = sptoken "then "
elsetoken =sptoken "else "
eqtoken = sptoken "=="
nulltoken =sptoken "null "
plus = sptoken "+"
minus = sptoken "-"
mult = sptoken "*"
slash = sptoken "/"
constoken = sptoken ":"
feqtoken = sptoken "="

bterm = sp *> (chainl appterm ((mult <@ const (f "*") ) <|> (slash <@ const (f "/") )))
aterm = sp *> (chainl bterm ((plus <@ const (f "+") ) <|> (minus <@ const (f "-") )))
f op = \x y -> App (App (Fname op) x) y 
lterm = sp *> (chainr aterm (constoken <@ const (f "cons")))
              
eqterm = sp*> lterm <*> (eqtoken  *> lterm ) <@ f
         <|> nulltoken  *> lterm <@ (App (Fname "null"))
         <|> lterm
         where f (x,y) = App (App (Fname "==") x) y

ifterm = (iftoken *> eqterm) <*> (thentoken *> expr) <*> (elsetoken *> expr) <@f
         <|> eqterm 
         where f (x1,(x2,x3)) = App (App (App (Fname "if") x1) x2) x3
         
expr=ifterm 

----------------fundefs

fargs = (symbol ' ') *> listOf (identifier) (symbol ' ') <|> succeed []

fundef::Parser Char Fundef                                                   
fundef = identifier <*> fargs  <*> (feqtoken *>  expr)	 <@ f
          where f (x,(y,z)) = Fun x y z
               
               

-- ---------------program

prog::Parser Char Program
prog =  (zeroOrMore (fundef <* (symbol '\n'))) <*>  expr <@f
        where f (x,y) = Prog x y
              
parse pgm = correctProgram (snd (head (prog pgm)))

-- For the expression part in all fundefs, if there exists "Fname argname" such that argname is a parameter name then replace "Fname argname" by "V argname"

correctProgram (Prog defs exp) = Prog (map (fundefCorrect []) defs) exp

fundefCorrect _ (Fun fname par exp) = Fun fname par (fundefCorrectExp par exp)
fundefCorrectExp par (App e1 e2) = App (fundefCorrectExp par e1) (fundefCorrectExp par e2)
fundefCorrectExp par (Fname argname) | argname `elem` par = V argname
                                     | otherwise = Fname argname
fundefCorrectExp _ x = x

-----------------------------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------

type Code = [Instn]

data Instn =	PUSH Int | PUSHINT Int | PUSHGLOBAL String |
		PUSHBOOL Bool | PUSHNIL | POP Int |
		EVAL | UNWIND | MKAP | UPDATE Int | RETURN |
		LABEL String | JUMP String | JFALSE String |
		ADD | SUB | MUL | DIV | CONS | HEAD | TAIL | IF | EQU |
		GLOBSTART String Int | PRINT | STOP 
--		| SLIDE Int

instance Show Instn where
	show (PUSH i) = "PUSH " ++ show i ++ "\n"			-----
	show (PUSHINT i) = "PUSHINT " ++ show i ++ "\n"			-----
	show (PUSHGLOBAL str) = "PUSHGLOBAL " ++ show str ++ "\n"	-----
	show (PUSHBOOL b) = "PUSHBOOL " ++ show b ++ "\n"		-----
	show PUSHNIL = "PUSHNIL " ++ "\n"				-----
	show (POP i) = "POP " ++ show i ++ "\n"				-----
	show EVAL = "EVAL" ++ "\n"					-----
	show UNWIND = "UNWIND" ++ "\n"					-----
	show MKAP = "MKAP" ++ "\n"					-----
	show RETURN = "RETURN" ++ "\n"					-----
	show (UPDATE i) = "UPDATE " ++ show i ++ "\n"			-----
	show (LABEL "MAIN") = "\n LABEL \"MAIN\"\n"			-----
	show (LABEL str) = "LABEL " ++ show str ++ "\n"			-----
	show (JUMP str) = "JUMP " ++ show str ++ "\n"			-----
	show (JFALSE str) = "JFALSE " ++ show str ++ "\n"		-----
	show ADD = "ADD" ++ "\n"					-----
	show SUB = "SUB" ++ "\n"					-----
	show MUL = "MUL" ++ "\n"					-----
	show DIV = "DIV" ++ "\n"					-----
	show CONS = "CONS" ++ "\n"					-----
	show HEAD = "HEAD" ++ "\n"					-----
	show TAIL = "TAIL" ++ "\n"					-----
	show IF = "IF" ++ "\n"
	show EQU = "EQU" ++ "\n"					-----
	show (GLOBSTART str i) = "\n GLOBSTART " ++ show str ++ " " ++ show i ++ "\n"	-----
	show PRINT = "PRINT" ++ "\n"
	show STOP = "STOP" ++ "\n"
--	show (SLIDE i) = "SLIDE " ++ show i ++ "\n"			-----

instance Eq Instn where
	PUSH i == PUSH j = i==j
	PUSHINT i == PUSHINT j = i==j
	PUSHGLOBAL i == PUSHGLOBAL j = i==j
	PUSHBOOL i == PUSHBOOL j = i==j
	PUSHNIL == PUSHNIL = True
	POP i == POP j = i==j
	EVAL == EVAL = True
	MKAP == MKAP = True
	RETURN == RETURN = True
	UPDATE i == UPDATE j = i==j
	LABEL i == LABEL j = i==j
	JUMP i == JUMP j = i==j
	JFALSE i == JFALSE j = i==j
	ADD == ADD = True
	SUB == SUB = True
	MUL == MUL = True
	CONS == CONS = True
	HEAD == HEAD = True
	TAIL == TAIL = True
	IF == IF = True
	EQU == EQU = True
	GLOBSTART i j == GLOBSTART k l = i==k && j==l
	PRINT == PRINT = True
	STOP == STOP = True
--	SLIDE i == SLIDE j = i==j
	_ == _ = False


gencpgm :: Program -> Code
gencpgm (Prog fdefs remexp) = (gen1 fdefs) ++ (gen2 remexp) ++ inbuilts

gen1 [] = []
gen1 (x:xs) = genf x ++ gen1 xs

gen2 x = LABEL "MAIN":genexp_c x [] 0++[EVAL, PRINT, STOP]

-- I had the following commented part to handle projection functions. I asked doubt on moodle but there was no positive response. so commented the following.

--genf (Fun name arglist (V v))	| elem v arglist = GLOBSTART name len:genexp_proj_r (V v) arglist len	-- elem always gives True
--								| otherwise = GLOBSTART name len:genexp_r (V v) arglist len			-- forbidden condition
--	where len = length arglist

genf (Fun name arglist exprs) = GLOBSTART name len:genexp_r exprs arglist len
	where len = length arglist

genexp_proj_r e l d = genexp_c e l d ++ [EVAL, UPDATE (d+1), POP d, RETURN]
genexp_r e l d = genexp_c e l d ++ [UPDATE (d+1), POP d, UNWIND]

genexp_c (App x y) list d = genexp_c y list d ++ genexp_c x list (d+1) ++ [MKAP]
genexp_c (V v) list d = [PUSH (depth v (reverse list) d 1)]
genexp_c (Fname f) _ _ = [PUSHGLOBAL f]
genexp_c (I i) _ _ = [PUSHINT i]
genexp_c (B b) _ _ = [PUSHBOOL b]
genexp_c (Nil) _ _ = [PUSHNIL]

--depth _ [] _ _ = d -- again forbidden condition
depth v (l:ls) d i 	| l==v = d-i
                   	| otherwise = depth v ls d (i+1)

inbuilts = consg++addg++subg++mulg++divg++eqg++headg++tailg++iteg++nullg

consg = [GLOBSTART "cons" 2, CONS, UPDATE 1, RETURN]
addg = [GLOBSTART "+" 2, PUSH 1, EVAL, PUSH 1, EVAL, ADD, UPDATE 3, POP 2, RETURN]
subg = [GLOBSTART "-" 2, PUSH 1, EVAL, PUSH 1, EVAL, SUB, UPDATE 3, POP 2, RETURN]
mulg = [GLOBSTART "*" 2, PUSH 1, EVAL, PUSH 1, EVAL, MUL, UPDATE 3, POP 2, RETURN]
divg = [GLOBSTART "/" 2, PUSH 1, EVAL, PUSH 1, EVAL, DIV, UPDATE 3, POP 2, RETURN]
eqg = [GLOBSTART "==" 2, PUSH 1, EVAL, PUSH 1, EVAL, EQU, UPDATE 3, POP 2, RETURN]
headg = [GLOBSTART "head" 1, EVAL, HEAD, EVAL, UPDATE 1, UNWIND]
tailg = [GLOBSTART "tail" 1, EVAL, TAIL, EVAL, UPDATE 1, UNWIND]
iteg = [GLOBSTART "if" 3, PUSH 0, EVAL, JFALSE "L1", PUSH 1, JUMP "L2", LABEL "L1", PUSH 2, LABEL "L2", EVAL, UPDATE 4, POP 3, UNWIND]
nullg = [GLOBSTART "null" 1, PUSHNIL, PUSH 1, EVAL, EQU, UPDATE 2, POP 1, RETURN]

	-- EVAL PUSHNIL EQU UPDATE 1 RETURN

----------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------

------------------------- HEAP -------------------------------------------

{--	The heap is represented as a triple, containing:
	the number of objects in the heap;
	a list of unused addresses;
	an association list mapping addresses to objects.
	Addresses are represented as numbers --}
type Heap a = (Int, [Addr], [(Addr, a)])
type Addr = Int

-- hInitial returns an initialised empty heap.
hInitial :: Heap a
hInitial = (0, [1..], [])

{--hAlloc takes a heap and an object, and returns a new heap and an address; the new heap is exactly the same as the old one, except that the
specified object is found at the address returned.--}
hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, (next:free), cts) n = ((size+1, free, (next, n):cts), next)

{--hUpdate takes a heap, an address and an object; it returns a new heap in which the address is now associated with the object. --}
hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, cts) a n = (size, free, (a,n):remove cts a)

{--hFree takes a heap and an address and returns a new heap with the specified object removed. --}
hFree :: Heap a -> Addr -> Heap a
hFree (size, free, cts) a = (size-1, a:free, remove cts a)

{--hLookup takes a heap and an address and returns the object associated with that address.--}
hLookup :: Heap a -> Addr -> a
hLookup (_, _, cts) a = aLookup cts a (error ("Can't find node" ++ showaddr a ++ "in heap.\n"))

{--hLookup takes a heap and an address and returns the object associated with that address.--}
--hLookup' :: Heap n -> Addr -> n
hLookup' (c, f, cts) a = case node of
				NInd a' -> hLookup' (c, f, cts) a'
				otherwise -> node
	where node = aLookup cts a (error ("Can't find node" ++ showaddr a ++ "in heap.\n")) 

{--hAddresses returns the addresses of all the objects in the heap. hSize returns the number of objects in the heap.--}
hAddresses :: Heap a -> [Addr]
hAddresses (size, _, cts) = [addr | (addr,node) <- cts]

{--hNull is an address guaranteed to differ from every address returned by hAlloc--}
hNull :: Addr
hNull = 0

{--hIsnull tells whether an address is this distinguished value.--}
hIsnull :: Addr -> Bool
hIsnull a = a == hNull

showaddr :: Addr -> [Char]
showaddr a = "#" ++ show a

hSize :: Heap a -> Int
hSize (size,_,_) = size

{--The auxiliary function remove removes an item from a heap contents--}
remove :: [(Addr,a)] -> Addr -> [(Addr,a)]
remove [] a = error ("Attempting to remove illegal address " ++ showaddr a ++ ".\n")
remove ((a',n):cts) a	| a == a' = cts
			| otherwise = (a',n):(remove cts a)

----------------------------- ASSOC ---------------------------------

type ASSOC a b	= [(a,b)]

aLookup :: (Eq a) => ASSOC a b -> a -> b -> b
aLookup cts a err = foldr f err cts
	where f (a',n) y = if a==a' then n else y

--aLookup [] a err = err
--aLookup ((a',n):cts) a err	| a == a' = n
--							| otherwise = aLookup cts a err

aDomain :: ASSOC a b -> [a]
aDomain alist = [a | (a,n) <- alist]

aRange :: ASSOC a b -> [b]
aRange alist = [n | (a,n) <- alist]

aEmpty :: ASSOC a b
aEmpty = []

{--
The abstract data type nameSupply acts as a supply of unique names. --}


{----
getName takes a name supply and a prefix string, and returns a depleted name supply together with a string which is a new unique name; this string has the specified prefix. getNames does the same thing for a list of prefixes. Finally, initialNameSupply is the initial, undepleted name supply.--}

type NameSupply = Int

initialNameSupply :: NameSupply
initialNameSupply = 0

getName :: NameSupply -> String -> (NameSupply, String)
getName name_supply prefix = (name_supply+1, makeName prefix name_supply)

getNames :: NameSupply -> [String] -> (NameSupply, [String])
getNames name_supply prefixes = (name_supply + length prefixes, zipWith makeName prefixes [name_supply..])

makeName :: String -> NameSupply -> String 
makeName prefix ns = prefix ++ "_" ++ show ns

---------------------------------------------------------------------------------------------------------

type GmState
	= (GmOutput,		-- Current Output
	   GmCode,		-- Current Instruction stream
	   GmStack,		-- Current Stack
	   GmDump,		-- Current Dump
	   GmHeap,		-- Heap of Nodes
	   GmGlobals,		-- Global addresses in heap
	   GmStats)		-- Statistics

type GmOutput = String
type GmCode = [Instn]
type GmStack = [Addr]
type GmDump = [GmDumpItem]
type GmHeap = Heap Node
type Name = String
type GmGlobals = ASSOC Name Addr
type GmStats = Int

type GmDumpItem = (GmCode, GmStack)

data Node = NNum Int | NAp Addr Addr | NGlobal Int GmCode | NInd Addr | NNil | NCons Addr Addr | NBool Bool	deriving Show

instance Eq Node where
	NNum i == NNum j = i==j
	NAp i j == NAp k l = i==k && j==l
	NGlobal i j == NGlobal k l = i==k && j==l
	NInd i == NInd j = i==j
	NNil == NNil = True
	NCons i j == NCons k l = i==k && j==l
	NBool i == NBool j = i==j
	_ == _ = False

getOutput :: GmState -> GmOutput
getOutput (o,_,_,_,_,_,_) = o

putOutput :: GmOutput -> GmState -> GmState
putOutput o (_, i, stack, dump, heap, globs, stats) = (o, i, stack, dump, heap, globs, stats)


getCode	:: GmState -> GmCode
getCode (_,i,_,_,_,_,_) = i

putCode	:: GmCode -> GmState -> GmState
putCode i (o, _, stack, dump, heap, globs, stats) = (o, i, stack, dump, heap, globs, stats)

getStack :: GmState -> GmStack
getStack (_,_,s,_,_,_,_) = s

putStack :: GmStack -> GmState -> GmState
putStack stack (o, i, _, dump, heap, globs, stats) = (o, i, stack, dump, heap, globs,stats)

getDump :: GmState -> GmDump
getDump (_,_,_,dump,_,_,_) = dump

putDump :: GmDump -> GmState -> GmState
putDump dump (o, i, stack, _, heap, globs, stats) = (o, i, stack, dump, heap, globs, stats)

getHeap :: GmState -> GmHeap
getHeap (_,_,_,_,heap,_,_)	= heap

putHeap :: GmHeap -> GmState -> GmState
putHeap heap (o, i, stack, dump, _, globs, stats) = (o, i, stack, dump, heap, globs, stats)

getGlobals :: GmState -> GmGlobals
getGlobals (_,_,_,_,_,globs,_) = globs

putGlobals :: GmGlobals -> GmState -> GmState
putGlobals globs (o, i, stack, dump, heap, _, stats) = (o, i, stack, dump, heap, globs, stats)

statInitial :: GmStats
statInitial = 0

statIncSteps :: GmStats -> GmStats
statIncSteps s = s+1

statgetSteps :: GmStats -> Int
statgetSteps s = s

getStats :: GmState -> GmStats
getStats (_,_,_,_,_,_,stats) = stats

putStats :: GmStats -> GmState -> GmState
putStats stats (o, i, stack, dump, heap, globals, _) = (o, i, stack, dump, heap, globals, stats)

eval :: GmState -> [GmState]
eval state = state:restState
	where restState	| gmFinal state = []
			| otherwise = eval nextState
	      nextState	= doAdmin (step state)

doAdmin :: GmState -> GmState
doAdmin s = putStats (statIncSteps (getStats s)) s

gmFinal :: GmState -> Bool
gmFinal s = case (getCode s) of
		[]		-> True
		otherwise	-> False

step :: GmState -> GmState
step state = dispatch i (putCode is state)
	where (i:is) = getCode state

dispatch :: Instn -> GmState -> GmState
dispatch i = case i of
		(PUSHGLOBAL f)	-> pushglobal f
		(PUSHINT n)	-> pushint n
		(PUSHBOOL b)	-> pushbool b
		MKAP		-> mkap
		(PUSH n)	-> push n
		UNWIND		-> unwind
--		(SLIDE n)	-> slide n
		(UPDATE n)	-> update n
		(POP n)		-> pop n
		RETURN		-> retrn
		ADD		-> add
		SUB		-> subtractn
		MUL		-> multiply
		DIV		-> divide
		EQU		-> equal
		EVAL		-> evaluate
		JUMP l		-> jump l
		JFALSE l	-> jfalse l
		LABEL _		-> id
		PRINT		-> printout
		STOP		-> stopall
		PUSHNIL		-> pushnil
		CONS		-> consop
		HEAD		-> headop
		TAIL		-> tailop

stopall :: GmState -> GmState
stopall state = putCode [] state

printout :: GmState -> GmState
printout state = case node of
			NNum n -> putOutput (o++"(Num "++show n++"):") (putStack as state)
			NBool b -> putOutput (o++"(Bool "++show b++"):") (putStack as state)
			NNil -> putOutput (o++"[].list. :") (putStack as state)
			NCons x y -> putCode (EVAL:PRINT:EVAL:PRINT:is) (putStack (x:y:as) state)
			x -> error ("Cant print "++show x)
	where (a:as) = getStack state
	      is = getCode state
	      o = getOutput state
	      heap = getHeap state
	      node = getnode a heap

pushglobal :: Name -> GmState -> GmState
pushglobal f state = putStack (a:getStack state) state
	where a = aLookup (getGlobals state) f (error ("Undeclared global " ++ f ++ ".\n"))

jump :: String -> GmState -> GmState
jump label state = putCode is' state
	where (_:is') = dropWhile (/=(LABEL label)) is
	      is = getCode state

jfalse :: String -> GmState -> GmState
jfalse label state = case (getnode a heap) of
			NBool False -> jump label (putStack as state)
			otherwise -> putStack as state
	where (a:as) = getStack state
	      heap = getHeap state


pushnil :: GmState -> GmState
pushnil state	| elem name (aDomain globs) = putStack (a:stack) state
		| otherwise = putGlobals ((name,a'):globs) (putHeap heap' (putStack (a':stack) state))
	where name = show NNil
	      globs = getGlobals state
	      stack = getStack state
	      (heap', a') = hAlloc (getHeap state) NNil
	      a = aLookup globs name (error "Nil not found.\n")


consop :: GmState -> GmState				--- Can we lookup in globals somehow?
consop state = putHeap heap' (putStack (a':as) state)
	where (a1:a2:as) = getStack state
	      (heap', a') = hAlloc (getHeap state) (NCons a1 a2)

headop :: GmState -> GmState
headop state = case hLookup (getHeap state) a of
		(NCons a1 a2) -> putStack (a1:as) state
		(NInd a') -> headop (putStack (a':as) state)	--- This case should never occur
		x -> error ("error in headop"++show x)
	where (a:as) = getStack state


tailop :: GmState -> GmState
tailop state = case hLookup (getHeap state) a of
		(NCons a1 a2) -> putStack (a2:as) state
		(NInd a') -> tailop (putStack (a':as) state)
	where (a:as) = getStack state

pushint :: Int -> GmState -> GmState
pushint n state	| elem name (aDomain globs) = putStack (a:stack) state
		| otherwise = putGlobals ((name,a'):globs) (putHeap heap' (putStack (a':stack) state))
	where name = show n
	      globs = getGlobals state
	      stack = getStack state
	      (heap', a') = hAlloc (getHeap state) (NNum n)
	      a = aLookup globs name (error "Int not found.\n")


pushbool :: Bool -> GmState -> GmState
pushbool b state	| elem name (aDomain globs) = putStack (a:stack) state
			| otherwise = putGlobals ((name,a'):globs) (putHeap heap' (putStack (a':stack) state))
	where name = show b
	      globs = getGlobals state
	      stack = getStack state
	      (heap', a') = hAlloc (getHeap state) (NBool b)
	      a = aLookup globs name (error "Bool not found.\n")

mkap :: GmState -> GmState
mkap state = putHeap heap (putStack (a:stack) state)
	where (heap, a) = hAlloc (getHeap state) (NAp a1 a2)
	      a1:a2:stack = getStack state

-- this was before stack rearrangement
--push :: Int -> GmState -> GmState
--push n state = putStack (a:as) state
--	where as = getStack state
--	      a	= getArg (hLookup (getHeap state) (as !! (n+1))

push :: Int -> GmState -> GmState
push n state = putStack ((as!!n):as) state
	where as = getStack state

--getArg :: Node -> Addr
--getArg (NAp a1 a2) = a2

--slide :: Int -> GmState -> GmState
--slide n state = putStack (a:drop n as) state
--	where (a:as) = getStack state

unwind :: GmState -> GmState
unwind state = newState (hLookup heap a)
	where (a:as) = getStack state
	      heap = getHeap state
	      ((is',as'):dump') = getDump state
	      newState (NNum n) = putDump dump' (putCode is' (putStack (a:as') state))
	      newState (NBool b) = putDump dump' (putCode is' (putStack (a:as') state))
	      newState (NCons a1 a2) = putDump dump' (putCode is' (putStack (a:as') state))
	      newState (NNil) = putDump dump' (putCode is' (putStack (a:as') state))
	      newState (NAp a1 a2) = putCode [UNWIND] (putStack (a1:a:as) state)
	      newState (NInd a1) = putCode [UNWIND] (putStack (a1:as) state)
	      newState (NGlobal n c)	| length as < n = putDump dump' (putCode is' (putStack ((last (a:as)):as') state))
				    	| otherwise = putCode c (putStack (rearrange (a:as) heap n) state)

rearrange (a:as) heap 0 = (a:as)
rearrange (a:b:as) heap n = a2:(rearrange (b:as) heap (n-1))
	where (NAp a1 a2) = (hLookup heap b)							

update :: Int -> GmState -> GmState
update n state = putHeap heap' (putStack as state)
	where (a:as) = getStack state
	      heap' = hUpdate (getHeap state) (as !! (n-1)) (NInd a)

pop :: Int -> GmState -> GmState
pop n state = putStack (drop n (getStack state)) state

retrn :: GmState -> GmState
retrn state = (putDump dump'.putCode is'.putStack ((last as):as')) state
	where ((is',as'):dump') = getDump state
	      as = getStack state		-- Usually should return singleton list

add :: GmState -> GmState
add state = pushint (i1+i2) (putStack as state)
	where a1:a2:as = getStack state
	      heap = getHeap state
	      i1 = getval a1 heap
	      i2 = getval a2 heap

subtractn :: GmState -> GmState
subtractn state = pushint (i1-i2) (putStack as state)
	where a1:a2:as = getStack state
	      heap = getHeap state
	      i1 = getval a1 heap
	      i2 = getval a2 heap

multiply :: GmState -> GmState
multiply state = pushint (i1*i2) (putStack as state)
	where a1:a2:as = getStack state
	      heap = getHeap state
	      i1 = getval a1 heap
	      i2 = getval a2 heap

divide :: GmState -> GmState
divide state = pushint (div i1 i2) (putStack as state)
	where a1:a2:as = getStack state
	      heap = getHeap state
	      i1 = getval a1 heap
	      i2 = getval a2 heap

equal :: GmState -> GmState
equal state = case (n1,n2,stack) of
		(NInd x, y,a1:a2:as) -> putCode (EQU:is) (putStack (x:a2:as) state)
		(x, NInd y,a1:a2:as) -> putCode (EQU:is) (putStack (a1:y:as) state)
--		(NInd x, y) -> putCode (EVAL:EQU:is) (putStack (a1:a2:as) state)
--		(x, NInd y) -> putCode (EVAL:EQU:is) (putStack (a2:a1:as) state)
		(NNum m, NNum n,a1:a2:as) -> pushbool (m==n) (putStack as state)
		(NBool a, NBool b,a1:a2:as) -> pushbool (a==b) (putStack as state)
		(NBool False, y,[a1,_,_,a4,a5,a6]) -> putStack ([a1,a4,a5,a6]) state
		(NBool True, y,[_,a2,a3,a4,a5,a6]) -> putCode (EQU:is) (putStack ([a2,a3,a4,a5,a6]) state)
--		(NNil, NNil) -> pushbool True (putStack as state)
		(NAp a b, y,a1:a2:as) -> putCode (EVAL:EQU:is) (putStack (a1:a2:as) state)
		(x, NAp a b,a1:a2:as) -> putCode (EVAL:EQU:is) (putStack (a2:a1:as) state)
--		(NNil, NCons x y) -> pushbool False (putStack as state)
--		(NCons u v, NNil) -> pushbool False (putStack as state)
		(NCons u v, NCons x y,a1:a2:as) -> putCode (EQU:EQU:is) (putStack (u:x:v:y:as) state)
		(x,y,a1:a2:as) -> pushbool (x==y) (putStack as state)
	where stack = getStack state
	      is = getCode state
	      heap = getHeap state
	      n1 = hLookup heap (stack!!0)
	      n2 = hLookup heap (stack!!1)

evaluate :: GmState -> GmState
evaluate state = case (hLookup heap a) of
			(NNum n) -> state
			(NBool b) -> state
			(NCons a1 a2) -> state
			(NNil) -> state
			(NGlobal 0 c') -> (putDump ((is,as):dump).putStack [a].putCode c') state
			(NGlobal n c') -> state		-- for non-CAF function node. program behaves correctly even if commented as Unwind alse takes care of it.
			(NInd a1) -> putCode (EVAL:is) (putStack (a1:as) state)		-- same here
			otherwise -> (putDump ((is,as):dump).putStack [a].putCode [UNWIND]) state
	where	is = getCode state
		(a:as) = getStack state
		dump = getDump state
		heap = getHeap state
		
---------------------------------------------------------------------------------------------------

code3 = [LABEL "MAIN", PUSHNIL]
code2 = [LABEL "MAIN", PUSHINT 50, PUSHINT 50, EQU, JFALSE "L1", PUSHINT 10, JUMP "L2", LABEL "L1", PUSHINT 20, LABEL "L2"]
code = [LABEL "MAIN", PUSHINT 100, PUSHGLOBAL "GETFUN", EVAL, MKAP, EVAL, GLOBSTART "GETFUN" 0, PUSHINT 50, PUSHGLOBAL "f2", MKAP, EVAL, UPDATE 1, RETURN, GLOBSTART "f2" 2, PUSH 1, EVAL, PUSH 1, EVAL, ADD, UPDATE 3, POP 2, RETURN]

showtrace = (eval.compile) code
out = runProg code

runProg :: GmCode -> String
runProg prog = (getOutput.last.eval.compile) prog

getval :: Addr -> GmHeap -> Int
getval addr heap = case hLookup heap addr of
			NNum a -> a
			NInd a -> getval a heap
			otherwise -> error "Getval returned non-number.\n"

getnode :: Addr -> GmHeap -> Node
getnode addr heap = case hLookup heap addr of
			NInd a -> getnode a heap
			NNum a -> NNum a
			NBool b -> NBool b
			NNil -> NNil
			NCons i j -> NCons i j
			NAp a b -> NAp a b
			a1 -> error ("Getnode returned "++(show a1)++".\n")

compile :: GmCode -> GmState
compile program	= ("", initialCode, [], [], heap, globals, statInitial) 
	where (heap,globals) = buildInitialHeap program

buildInitialHeap :: GmCode -> (GmHeap, GmGlobals)
buildInitialHeap program = mapAccumL allocateSc hInitial compiled
	where compiled = (mycompile.modcode) program

-- Replaces LABEL "MAIN" with GLOBSTART "MAIN" 0
modcode :: GmCode -> GmCode
modcode code = map f code
	where f x = if x==(LABEL "MAIN") then (GLOBSTART "MAIN" 0) else x

type GmCompiledSC = (Name, Int, GmCode)

mycompile :: GmCode -> [GmCompiledSC]
mycompile [] = []
mycompile ((GLOBSTART str n):xs) = (str,n,takeWhile isnotGlobStart xs):mycompile xs
	where isnotGlobStart x = case x of
				GLOBSTART s n -> False
				otherwise -> True
mycompile (x:xs) = mycompile xs

allocateSc :: GmHeap -> GmCompiledSC -> (GmHeap, (Name, Addr))
allocateSc heap (name, nargs, instns) = (heap', (name, addr))
	where (heap', addr) = hAlloc heap (NGlobal nargs instns)

initialCode :: GmCode
initialCode = [PUSHGLOBAL "MAIN", UNWIND]

{--

type CoreProgram = [(Name, [Name], CoreExpr)]

compile :: CoreProgram -> GmState
compile program	= (initialCode, [], heap, globals, statInitial) 
		where (heap,globals) = buildInitialHeap program

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program = mapAccumL allocateSc hInitial compiled
	where compiled = map compileSc program
	where compiled = map compileSc (preludeDefs ++ program) ++ compiledPrimitives

compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSC
compileSc (name, env, body) = (name, length env, compileR body (zip env [0..]))

type GmCompiler = CoreExpr -> GmEnvironment -> GmCode

compileR		:: GmCompiler
compileR e env		= compileC e env ++ [SLIDE (length env + 1), UNWIND]

type CoreExpr		= Exp
type GmEnvironment	= ASSOC Name Int

compileC :: GmCompiler
compileC (V v) env	| elem v (aDomain env)	= [PUSH n]
			| otherwise = [PUSHGLOBAL v]
			where n = aLookup env v (error "Cant happen")
compileC (I n) env		= [PUSHINT n]
compileC (App e1 e2) env	= compileC e2 env ++ compileC e1 (argOffset 1 env) ++ [MKAP]

argOffset		:: Int -> GmEnvironment -> GmEnvironment
argOffset n env		= [(v, n+m) | (v,m) <- env]


--[("main",0,[PUSHINT 21,PUSHGLOBAL "double",MKAP,SLIDE 1,UNWIND]),
--("double",1,[PUSH 0,PUSH 1,PUSHGLOBAL "+",MKAP,MKAP,SLIDE 2,UNWIND])]
--}

{--
showResults :: [GmState] -> [Char]
showResults states = "SuperCombinator def"++"\n" ++ show (map (showSC s) (getGlobals s)) ++ "\n"++"State transitions"++"\n" ++ show (map showState states) ++ "\n" ++ showStats (last states)
	where (s:ss) = states

showHeap (x,y,z) = show x ++ show (take 2 y) ++ show z
showHeapPair (x, y) = "(" ++ showHeap x ++ "," ++ show y ++ ")"
showBuildHeap (x,y) = "(" ++ showHeap x ++ show y ++ ")"

showSC :: GmState -> (Name, Addr) -> [Char]
showSC s (name, addr) = "Code For " ++ name ++ "\n" ++ showInstructions code ++ "\n"
			where (NGlobal arity code) = (hLookup (getHeap s) addr)

showInstructions :: GmCode -> [Char]
showInstructions is = "Code:{\n" ++ show is ++ "}\n"

showState :: GmState -> [Char]
showState s = showStack s ++ "\n" ++ showInstructions (getCode s) ++ "\n"

showStack :: GmState -> [Char]
showStack s = "Stack:[" ++ show (map (showStackItem s) (reverse (getStack s))) ++ "]\n"

showStackItem :: GmState -> Addr -> [Char]
showStackItem s a = (showaddr a) ++ ": " ++ showNode s a (hLookup (getHeap s) a)

showNode :: GmState -> Addr -> Node -> [Char]
showNode s a (NNum n) = "Num " ++ show n
showNode s a (NAp a1 a2) = "App" ++ showaddr a1 ++ showaddr a2
showNode s a (NGlobal n g) = "Global " ++ show v
	where v = head [n | (n,b) <- getGlobals s, a == b]
showNode s a (NInd a') = "Iniderction"++showaddr a'

showStats :: GmState -> [Char]
showStats s = "Steps taken = " ++ show (getStats s)
--}

main = do
	input <- readFile "pfile"
	let
		output = (runProg.gencpgm.parse) input
--		trace = (eval.compile.gencpgm.parse) input
		--
--	print trace	-- Donot uncomment as it also prints heap which is infinite list
	print output

gcode = do
	input <- readFile "pfile"
	let
		output = (gencpgm.parse) input
	print output
