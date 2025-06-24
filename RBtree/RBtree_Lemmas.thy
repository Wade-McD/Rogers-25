theory RBtree_Lemmas
  imports RBtree
begin

text \<open>Structural invariants\<close>

text \<open>Characterizes that a color not being Black implies it must be Red.\<close>
lemma neq_Black[simp]: "(c \<noteq> Black) = (c = Red)"
  by (cases c) auto

find_theorems name: tree.induct
find_theorems name: tree.exhaust

text \<open>Specialized induction and case analysis rules for trees of pairs.\<close>
lemmas tree2_induct = tree.induct[where 'a = "'a \<times> 'b", split_format (complete)]
lemmas tree2_cases = tree.exhaust[where 'a = "'a \<times> 'b", split_format(complete)]
                         
text \<open>Lifts the simpler invariant `invc` to the stronger `invc2`.\<close>
lemma invc2I: "invc t \<Longrightarrow> invc2 t"
  apply(cases t rule: tree2_cases)
  by simp+

text \<open>Painting any tree with Black gives a tree with Black at the root.\<close>
lemma color_paint_Black : "get_color (paint Black t) = Black"
  by (cases t) auto

text \<open>Successive painting overrides previous colorings; only the outer color matters.\<close>
lemma paint2: "paint c2 (paint c1 t) = paint c2 t"
  by (cases t) auto

text \<open>Height invariants are preserved when the color of a node is changed.\<close>
lemma invh_paint: "invh t \<Longrightarrow> invh (paint c t)"
  by (cases t) auto

text \<open>Balancing a left-heavy tree maintains the color invariant.\<close>
lemma invc_baliL: "\<lbrakk>invc2 l; invc r\<rbrakk> \<Longrightarrow> invc (baliL l a r)"
  by (induct l a r rule: baliL.induct) auto

text \<open>Balancing a right-heavy tree maintains the color invariant.\<close>
lemma invc_baliR: "\<lbrakk>invc l; invc2 r\<rbrakk> \<Longrightarrow> invc (baliR l a r)"
  by(induct l a r rule: baliR.induct) auto

text \<open>After balancing, the black-height increases by one if subtrees were equal.\<close>
lemma bh_baliL: "bh l = bh r \<Longrightarrow> bh (baliL l a r) = Suc (bh l)"
  by (induct l a r rule: baliL.induct) auto

lemma bh_baliR: "bh l = bh r \<Longrightarrow> bh (baliR l a r) = Suc (bh l)"
  by (induct l a r rule: baliR.induct) auto

text \<open>Balancing preserves height invariants.\<close>
lemma invh_baliL: "\<lbrakk>invh l; invh r; bh l = bh r\<rbrakk> \<Longrightarrow> invh(baliL l a r)"
  by (induct l a r rule: baliL.induct)auto

lemma invh_baliR: "\<lbrakk>invh l; invh r; bh l = bh r\<rbrakk> \<Longrightarrow> invh(baliR l a r)"
  by (induct l a r rule: baliR.induct)auto

text \<open>Combines all balancing-related invariants for `baliR`.\<close>
lemma inv_baliR: 
  "\<lbrakk>invh l; invh r; invc l; invc2 r; bh l = bh r\<rbrakk> \<Longrightarrow> 
    invc (baliR l a r) \<and> invh (baliR l a r) \<and> bh (baliR l a r) = Suc (bh l)"
  by (induct l a r rule: baliR.induct) auto

text \<open>Combines all balancing-related invariants for `baliL`.\<close>
lemma inv_baliL: 
  "\<lbrakk>invh l; invh r; invc2 l; invc r; bh l = bh r\<rbrakk> \<Longrightarrow> 
    invc (baliL l a r) \<and> invh (baliL l a r) \<and> bh (baliL l a r) = Suc (bh l)"
  by (induct l a r rule: baliL.induct) auto


text\<open>Insertion\<close>

text \<open>Insertion maintains the color invariants, considering whether the root was black.\<close>
lemma invc_ins: "invc t \<longrightarrow> invc2 (ins x t) \<and> (get_color t = Black \<longrightarrow> invc (ins x t))"
  apply(induct x t rule: ins.induct)
    apply(auto simp: invc_baliL invc_baliR invc2I)
  by (simp add: cmp_def invc2I invc_baliL invc_baliR)+

text \<open>Insertion maintains the height invariant and black-height.\<close>
lemma invh_ins: "invh t \<Longrightarrow> invh (ins x t) \<and> bh (ins x t) = bh t"
  apply(induct x t rule: ins.induct)
    apply(auto simp: invh_baliL invh_baliR bh_baliL bh_baliR)
     apply (simp add: cmp_def invh_baliL invh_baliR)
  by (simp add: bh_baliL bh_baliR cmp_def)+

text \<open>Insertion preserves full red-black tree invariants.\<close>
theorem rbt_insert: "rbt t \<Longrightarrow> rbt (insert x t)"
  by (simp add: invc_ins invh_ins color_paint_Black invh_paint rbt_def insert_def)

text \<open>All insertion invariants together: height, color, black-height.\<close>
lemma inv_ins: "\<lbrakk>invc t; invh t\<rbrakk> \<Longrightarrow> 
  invc2 (ins x t) \<and> (get_color t = Black \<longrightarrow> invc (ins x t)) \<and> invh (ins x t) \<and> bh (ins x t) = bh t"
  apply(induct x t rule: ins.induct)
    apply(auto simp: inv_baliL inv_baliR invc2I)
        apply (metis color.distinct(1) ins.simps(2) invc.simps(2) invc_ins)
       apply (simp add: cmp_def invc_baliL invc_baliR)
      apply (simp add: cmp_def invh_baliL invh_baliR)
     apply (metis Suc_eq_plus1 bh.simps(2) ins.simps(2) invh.simps(2) invh_ins)
  by (simp add: cmp_def)+

text \<open>Alternative proof for insertion correctness.\<close>
theorem rbt_insert2: "rbt t \<Longrightarrow> rbt (insert x t)"
  by (simp add: inv_ins color_paint_Black invh_paint rbt_def insert_def)

text\<open>Deletion\<close>

text \<open>Painting a black root red decreases the black-height by one.\<close>
lemma bh_paint_Red: "get_color t = Black \<Longrightarrow> bh (paint Red t) = bh t-1"
  by (cases t) auto

text \<open>Shows that balancer `baldL` preserves height invariant and computes black-height correctly.\<close>
lemma invh_baldL_invc: "\<lbrakk>invh l; invh r; bh l+1 = bh r; invc r\<rbrakk> \<Longrightarrow>
  invh (baldL l a r) \<and> bh (baldL l a r) = bh r"
  apply(induction l a r rule: baldL.induct)
  by (auto simp: invh_baliR invh_paint bh_baliR bh_paint_Red)

text \<open>Special case of `baldL` correctness when right child is black.\<close>
lemma invh_baldL_Black:
  "\<lbrakk>invh l; invh r; bh l+1 = bh r; get_color r = Black\<rbrakk> \<Longrightarrow> invh (baldL l a r) \<and> bh (baldL l a r) = bh r"
  apply(induct l a r rule: baldL.induct)
  by (auto simp add: invh_baliR bh_baliR)

text \<open>`baldL` preserves the color invariants.\<close>
lemma invc_baldL: "\<lbrakk>invc2 l; invc r; get_color r = Black\<rbrakk> \<Longrightarrow> invc (baldL l a r)"
  apply(induct l a r rule: baldL.induct)
  by (simp_all add: invc_baliR)

text \<open>Strengthens `invc` preservation to `invc2` for `baldL`.\<close>
lemma invc2_baldL: "\<lbrakk>invc2 l; invc r\<rbrakk> \<Longrightarrow> invc2 (baldL l a r)"
  apply(induct l a r rule: baldL.induct)
  by (auto simp: invc_baliR paint2 invc2I)

text \<open>`baldR` preserves height and black-height under similar conditions as `baldL`.\<close>
lemma invh_baldR_invc:
  "\<lbrakk>invh l; invh r; bh l = bh r + 1; invc l\<rbrakk> \<Longrightarrow> invh (baldR l a r) \<and> bh (baldR l a r) = bh l"
  apply(induct l a r rule: baldR.induct)
  by (auto simp: invh_baliL bh_baliL invh_paint bh_paint_Red)

text \<open>`baldR` maintains color invariants.\<close>
lemma invc_baldR: "\<lbrakk>invc l; invc2 r; get_color l = Black\<rbrakk> \<Longrightarrow> invc (baldR l a r)"
  by (induct l a r rule: baldR.induct) (simp_all add: invc_baliL)

lemma invc2_baldR: "\<lbrakk>invc l; invc2 r\<rbrakk> \<Longrightarrow> invc2 (baldR l a r)"
  by (induct l a r rule: baldR.induct) (auto simp: invc_baliL paint2 invc2I)

text \<open>`join` preserves height invariants and correctly computes black-height.\<close>
lemma invh_join:
  "\<lbrakk>invh l; invh r; bh l = bh r\<rbrakk> \<Longrightarrow> invh (join l r) \<and> bh (join l r) = bh l"
  by (induct l r rule: join.induct) (auto simp: invh_baldL_Black split: tree.splits color.splits)

text \<open>`join` maintains both color invariants, including special case if both roots are Black.\<close>
lemma invc_join:
  "\<lbrakk>invc l; invc r\<rbrakk> \<Longrightarrow> (get_color l = Black \<and> get_color r = Black \<longrightarrow> invc (join l r)) \<and> invc2 (join l r)"
  by (induct l r rule: join.induct) (auto simp: invc_baldL invc2I split: tree.splits color.splits)

text \<open>All invariants for `baldL` summarized in a single lemma.\<close>
lemma inv_baldL:
  "\<lbrakk>invh l; invh r; bh l+1 = bh r; invc2 l; invc r\<rbrakk>
    \<Longrightarrow> invh (baldL l a r) \<and> bh (baldL l a r) = bh r \<and> invc2 (baldL l a r) \<and> 
    (get_color r = Black \<longrightarrow> invc (baldL l a r))"
  by (induct l a r rule: baldL.induct) (auto simp: inv_baliR invh_paint bh_baliR bh_paint_Red paint2 invc2I)

text \<open>All invariants for `baldR` summarized in a single lemma.\<close>
lemma inv_baldR:
  "\<lbrakk>invh l; invh r; bh l = bh r+1; invc2 r; invc l\<rbrakk>
    \<Longrightarrow> invh (baldR l a r) \<and> bh (baldR l a r) = bh l \<and> invc2 (baldR l a r) \<and> 
    (get_color l = Black \<longrightarrow> invc (baldR l a r))"
  by (induct l a r rule: baldR.induct) (auto simp: inv_baliL invh_paint bh_baliL bh_paint_Red paint2 invc2I)

text \<open>Summarizes all correctness invariants for `join`.\<close>
lemma inv_join:
  "\<lbrakk>invh l; invh r; bh l = bh r; invc l; invc r\<rbrakk>
   \<Longrightarrow> invh (join l r) \<and> bh (join l r) = bh l \<and> invc2 (join l r) \<and> (get_color l = Black \<and> get_color r = Black \<longrightarrow> invc (join l r))"
  by (induct l r rule: join.induct) (auto simp: invh_baldL_Black inv_baldL invc2I split: tree.splits color.splits)

text \<open>Helper lemma: Any non-empty tree must be a binary node.\<close>
lemma neq_LeafD: "t \<noteq> \<langle>\<rangle> \<Longrightarrow> \<exists>l x c r. t = \<langle>l, (x,c), r\<rangle>"
  by (cases t rule: tree2_cases) auto

text \<open>Summarizes all deletion invariants depending on the color of the root.\<close>
lemma inv_del: "\<lbrakk>invh t; invc t\<rbrakk> \<Longrightarrow>
  invh (del_join x t) \<and>
  (get_color t = Red \<longrightarrow> bh (del_join x t) = bh t \<and> invc (del_join x t)) \<and>
  (get_color t = Black \<longrightarrow> bh (del_join x t) = bh t - 1 \<and> invc2 (del_join x t))"
  apply(induct x t rule: del_join.induct) 
  apply(auto simp: inv_baldL inv_baldR inv_join dest!: neq_LeafD)
  sorry

text \<open>Deletion preserves red-black tree invariants.\<close>
theorem rbt_delete: "rbt t \<Longrightarrow> rbt (delete x t)"
  by (metis delete_def rbt_def color_paint_Black inv_del invh_paint)

end
