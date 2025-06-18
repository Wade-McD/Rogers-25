theory RBtree
imports Main "HOL-Library.Tree"
begin

text \<open>Red-Black Trees with Invariants and Insertion\<close>

text \<open>cmp\<close>
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

(* --- TO DO --- *)
lemma height_bound:
  assumes "invc t" "invh t"
  shows "height t \<le> 2 * bh t + (if get_color t = Black then 0 else 1)"
  using assms
proof (induction t)
  case Leaf
  then show ?case by simp
next
  oops
qed

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

definition invc2 :: "'a rbt \<Rightarrow> bool" where
  "invc2 t \<equiv> invc (paint Black t)"

(* --- TO DO --- *)
lemma invc_ins: "invc t \<Longrightarrow> invc2 (ins x t)"
  oops

(* --- TO DO --- *)
lemma invh_ins: "invh t \<Longrightarrow> invh (ins x t)"
  oops
(* --- TO DO --- *)
theorem rbt_insert: "rbt t \<Longrightarrow> rbt (insert x t)"
  oops



fun baldR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "baldR t1 a (R t2 b t3) = R t1 a (B t2 b t3)"
| "baldR (B t1 a t2) b t3 = baliL (R t1 a t2) b t3"
| "baldR (R t1 a (B t2 b t3)) c t4 = R (baliL (paint Red t1) a t2) b (B t3 c t4)"
| "baldR t1 a t2 = R t1 a t2"

fun baldL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "baldL (R t1 a t2) b t3 = R (B t1 a t2) b t3"
| "baldL t1 a (B t2 b t3) = baliR t1 a (R t2 b t3)"
| "baldL t1 a (R (B t2 b t3) c t4) = R (B t1 a t2) b (baliR t3 c (paint Red t4))"
| "baldL t1 a t2 = R t1 a t2"

(* --- TO DO --- *)
lemma baldL_preserves:
  assumes "invh l" "invh r" "bh l + 1 = bh r"
      and "invc2 l" "invc r" "t' = baldL l a r"
  shows "invh t' \<and> bh t' = bh r \<and> invc2 t' \<and> (get_color r = Black \<longrightarrow> invc t')"
  using assms oops

(* --- TO DO --- *)
lemma baldR_preserves:
  assumes "invh l" "invh r" "bh l = bh r + 1"
      and "invc l" "invc2 r" "t' = baldR l a r"
  shows "invh t' \<and> bh t' = bh l \<and> invc2 t' \<and> (get_color l = Black \<longrightarrow> invc t')"
  using assms oops

fun split_min :: "'a rbt \<Rightarrow> 'a \<times> 'a rbt" where
  "split_min \<langle>l,(a,_),r\<rangle> =
     (if l = \<langle>\<rangle> then (a, r)
      else let (x, l') = split_min l in
        (x, if get_color l = Black then baldL l' a r else R l' a r))"

(* --- TO DO --- *)
lemma split_min_preserves:
  assumes "split_min t = (x, t')" "t \<noteq> \<langle>\<rangle>" "invh t" "invc t"
  shows "invh t' \<and> 
         (get_color t = Red \<longrightarrow> bh t' = bh t \<and> invc t') \<and>
         (get_color t = Black \<longrightarrow> bh t' = bh t - 1 \<and> invc2 t')"
  using assms
  oops



fun del :: "'a :: linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "del _ \<langle>\<rangle> = \<langle>\<rangle>"
| "del x \<langle>l,(a,_),r\<rangle> = (case cmp x a of
    LT \<Rightarrow> let l' = del x l
          in if l \<noteq> \<langle>\<rangle> \<and> get_color l = Black then baldL l' a r else R l' a r
  | EQ \<Rightarrow> if r = \<langle>\<rangle> then l 
          else let (a',r') = split_min r
               in if get_color r = Black then baldR l a' r' else R l a' r'  
  | GT \<Rightarrow> let r' = del x r 
          in if r \<noteq> \<langle>\<rangle> \<and> get_color r = Black then baldR l a r' else R l a r')"

(* --- TO DO --- *)
lemma del_preserves:
  assumes "invh t" "invc t" "t' = del x t"
  shows "invh t' \<and> 
         (get_color t = Red \<longrightarrow> bh t' = bh t \<and> invc t') \<and>
         (get_color t = Black \<longrightarrow> bh t' = bh t - 1 \<and> invc2 t')"
  using assms
  oops


definition delete :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "delete x t \<equiv> paint Black (del x t)"

(* --- TO DO --- *)
lemma rbt_delete : "rbt t \<Longrightarrow> rbt (delete x t)"
  oops

end