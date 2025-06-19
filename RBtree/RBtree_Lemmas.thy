theory RBtree_Lemmas
  imports RBtree
begin

(* --- TO DO --- *)
text \<open>Bound the overall height in terms of black height\<close>
lemma height_bound:
  assumes "invc t" "invh t"
  shows "height t \<le> 2 * bh t + (if get_color t = Black then 0 else 1)"
  using assms apply (auto) oops

find_theorems name: tree.induct
find_theorems name: tree.exhaust

lemmas tree2_induct = tree.induct[where 'a = "'a \<times> 'b", split_format (complete)]
lemmas tree2_cases = tree.exhaust[where 'a = "'a \<times> 'b", split_format(complete)]
                         
lemma invc2I: "invc t \<Longrightarrow> invc2 t"
  apply(cases t rule: tree2_cases)
  by simp+

lemma color_paint_Black : "get_color (paint Black t) = Black"
  by (cases t) auto

(* --- TO DO --- *)
text \<open>Insertion preserves the color invariant (weakened)\<close>
lemma invc_ins: "invc t \<Longrightarrow> invc2 (ins x t)"
  apply(cases t rule: tree2_cases)
   apply simp
  oops

(* --- TO DO --- *)
text \<open>Insertion preserves the height invariant\<close>
lemma invh_ins: "invh t \<Longrightarrow> invh (ins x t)"
  oops

(* --- TO DO --- *)
text \<open>Insertion preserves red-black tree validity\<close>
theorem rbt_insert: "rbt t \<Longrightarrow> rbt (insert x t)"
  oops

(* --- TO DO --- *)
text \<open>baldL preserves invariants\<close>
lemma baldL_preserves:
  assumes "invh l" "invh r" "bh l + 1 = bh r"
      and "invc2 l" "invc r" "t' = baldL l a r"
  shows "invh t' \<and> bh t' = bh r \<and> invc2 t' \<and> (get_color r = Black \<longrightarrow> invc t')"
  using assms oops

(* --- TO DO --- *)
text \<open>baldR preserves invariants\<close>
lemma baldR_preserves:
  assumes "invh l" "invh r" "bh l = bh r + 1"
      and "invc l" "invc2 r" "t' = baldR l a r"
  shows "invh t' \<and> bh t' = bh l \<and> invc2 t' \<and> (get_color l = Black \<longrightarrow> invc t')"
  using assms oops

(* --- TO DO --- *)
text \<open>deletion preserves red-black invariants (weakened)\<close>
lemma del_preserves:
  assumes "invh t" "invc t" "t' = del_join x t"
  shows "invh t' \<and> 
         (get_color t = Red \<longrightarrow> bh t' = bh t \<and> invc t') \<and>
         (get_color t = Black \<longrightarrow> bh t' = bh t - 1 \<and> invc2 t')"
  using assms
  oops

(* --- TO DO --- *)
text \<open>delete preserves red-black tree validity\<close>
lemma rbt_delete : "rbt t \<Longrightarrow> rbt (delete x t)"
  oops

(* --- TO DO --- *)
text \<open>join preserves red-black invariants\<close>
lemma join_invariants:
  assumes "invh l" "invh r" "bh l = bh r"
      and "invc l" "invc r"
      and "t' = join l r"
  shows "invh t' \<and> bh t' = bh l \<and> invc2 t' \<and> (get_color l = Black \<and> get_color r = Black \<longrightarrow> invc t')"
  oops

end