theory RBtree
imports Main "HOL-Library.Tree"
begin

text \<open>Red-Black Trees with Invariants and Insertion\<close>

(* This defines a simple enumeration type with three possible values:
   This type is used to model the result of a comparison between two values *)
datatype cmp_val = LT | EQ | GT

(* 'a::linorder - means that the type variable 'a is constrained to belong to the linorder 
   type class — i.e., it must support a linear (total) order.*)
definition cmp :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> cmp_val" where
  "cmp x y = (if x < y then LT else if x = y then EQ else GT)"

text \<open>Colored binary tree (red-black tree)\<close>

datatype color = Red | Black
type_synonym 'a rbt = "('a \<times> color) tree"

text \<open>Smart constructors for red and black nodes\<close>
abbreviation R where "R l a r \<equiv> \<langle>l, (a, Red), r\<rangle>"
abbreviation B where "B l a r \<equiv> \<langle>l, (a, Black), r\<rangle>"

text \<open>Extract the color of a node\<close>
fun get_color :: "'a rbt \<Rightarrow> color" where
  "get_color \<langle>\<rangle> = Black"
| "get_color \<langle>_,(_,c),_\<rangle> = c"

text \<open>Change the color of a node\<close>
fun paint :: "color \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "paint _ \<langle>\<rangle> = \<langle>\<rangle>"
| "paint c \<langle>l,(a,_),r\<rangle> = \<langle>l,(a,c),r\<rangle>"

text \<open>Color invariant: red nodes must have black children\<close>
fun invc :: "'a rbt \<Rightarrow> bool" where
  "invc \<langle>\<rangle> = True"
| "invc \<langle>l, (_,c),r\<rangle> 
        = ((c = Red \<longrightarrow> get_color l = Black \<and> get_color r = Black) \<and> invc l \<and> invc r)"

text \<open>Black-height: number of black nodes on the leftmost path\<close>
(*
   - Although bh traverses only the left spine of the tree, the fact that 
     invh traverses the complete tree ensures that all paths from the root to a leaf
     are considered
 *)
fun bh :: "'a rbt \<Rightarrow> nat" where
  "bh \<langle>\<rangle> = 0"
| "bh \<langle>l,(_,c),_\<rangle> = (if c = Black then bh l + 1 else bh l)"

text \<open>Height invariant: all paths from root to leaf have the same black height\<close>
fun invh :: "'a rbt \<Rightarrow> bool" where
  "invh \<langle>\<rangle> = True"
| "invh \<langle>l,(_,_),r\<rangle> = (bh l = bh r \<and> invh l \<and> invh r)"

text \<open>A valid red-black tree satisfies color and height invariants and has a black root\<close>
definition rbt :: "'a rbt \<Rightarrow> bool" where
  "rbt t \<equiv> invc t \<and> invh t \<and> get_color t = Black"

text \<open>Balancing after insertion on the left\<close>
fun baliL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "baliL (R (R t1 a t2) b t3) c t4 = R (B t1 a t2) b (B t3 c t4)"
| "baliL (R t1 a (R t2 b t3)) c t4 = R (B t1 a t2) b (B t3 c t4)"
| "baliL l a r = B l a r"

text \<open>Balancing after insertion on the right\<close>
fun baliR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "baliR l a (R t1 b (R t2 c t3)) = R (B l a t1) b (B t2 c t3)"
| "baliR l a (R (R t1 b t2) c t3) = R (B l a t1) b (B t2 c t3)"
| "baliR l a r = B l a r"

text \<open>Insertion into red-black tree\<close>
fun ins :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "ins x \<langle>\<rangle> = R \<langle>\<rangle> x \<langle>\<rangle>"
| "ins x (B l a r) = (case cmp x a of
    LT \<Rightarrow> baliL (ins x l) a r
  | EQ \<Rightarrow> B l a r
  | GT \<Rightarrow> baliR l a (ins x r))"
| "ins x (R l a r) = (case cmp x a of
    LT \<Rightarrow> R (ins x l) a r
  | EQ \<Rightarrow> R l a r
  | GT \<Rightarrow> R l a (ins x r))"

definition insert :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "insert x t \<equiv> paint Black (ins x t)"

end