theory RBT_set_opt
  imports "HOL-Library.RBT_Impl" "Containers.Set_Impl"
begin

type_synonym 'a urbt = "('a, unit) RBT_Impl.rbt"

definition is_empty :: "'a urbt \<Rightarrow> bool" where
  "is_empty t \<longleftrightarrow> (case t of RBT_Impl.Empty \<Rightarrow> True | _ \<Rightarrow> False)"

lemma is_empty_prop[simp]: "is_empty t \<longleftrightarrow> t = RBT_Impl.Empty"
  by (auto simp: is_empty_def split: RBT_Impl.rbt.splits)

definition small_rbt :: "'a urbt \<Rightarrow> bool" where
  "small_rbt t \<longleftrightarrow> bheight t < 6"

definition flip_rbt :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> bool" where
  "flip_rbt t1 t2 \<longleftrightarrow> bheight t2 < bheight t1"

abbreviation MR where "MR l a r \<equiv> Branch RBT_Impl.R l a () r"
abbreviation MB where "MB l a r \<equiv> Branch RBT_Impl.B l a () r"

fun baliL :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "baliL (MR (MR t1 a t2) b t3) c t4 = MR (MB t1 a t2) b (MB t3 c t4)"
| "baliL (MR t1 a (MR t2 b t3)) c t4 = MR (MB t1 a t2) b (MB t3 c t4)"
| "baliL t1 a t2 = MB t1 a t2"

fun baliR :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "baliR t1 a (MR t2 b (MR t3 c t4)) = MR (MB t1 a t2) b (MB t3 c t4)"
| "baliR t1 a (MR (MR t2 b t3) c t4) = MR (MB t1 a t2) b (MB t3 c t4)"
| "baliR t1 a t2 = MB t1 a t2"

fun paint :: "color \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "paint c RBT_Impl.Empty = RBT_Impl.Empty"
| "paint c (RBT_Impl.Branch _ l a () r) = RBT_Impl.Branch c l a () r"

fun baldL :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "baldL (MR t1 a t2) b t3 = MR (MB t1 a t2) b t3"
| "baldL t1 a (MB t2 b t3) = baliR t1 a (MR t2 b t3)"
| "baldL t1 a (MR (MB t2 b t3) c t4) = MR (MB t1 a t2) b (baliR t3 c (paint RBT_Impl.R t4))"
| "baldL t1 a t2 = MR t1 a t2"

fun baldR :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "baldR t1 a (MR t2 b t3) = MR t1 a (MB t2 b t3)"
| "baldR (MB t1 a t2) b t3 = baliL (MR t1 a t2) b t3"
| "baldR (MR t1 a (MB t2 b t3)) c t4 = MR (baliL (paint RBT_Impl.R t1) a t2) b (MB t3 c t4)"
| "baldR t1 a t2 = MR t1 a t2"

fun app :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "app RBT_Impl.Empty t = t"
| "app t RBT_Impl.Empty = t"
| "app (MR t1 a t2) (MR t3 c t4) = (case app t2 t3 of
    MR u2 b u3 \<Rightarrow> (MR (MR t1 a u2) b (MR u3 c t4))
  | t23 \<Rightarrow> MR t1 a (MR t23 c t4))"
| "app (MB t1 a t2) (MB t3 c t4) = (case app t2 t3 of
    MR u2 b u3 \<Rightarrow> MR (MB t1 a u2) b (MB u3 c t4)
  | t23 \<Rightarrow> baldL t1 a (MB t23 c t4))"
| "app t1 (MR t2 a t3) = MR (app t1 t2) a t3"
| "app (MR t1 a t2) t3 = MR t1 a (app t2 t3)"

fun rbt_joinL :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "rbt_joinL l x r = (if bheight l \<ge> bheight r then MR l x r
    else case r of MB l' x' r' \<Rightarrow> baliL (rbt_joinL l x l') x' r'
    | MR l' x' r' \<Rightarrow> MR (rbt_joinL l x l') x' r')"

fun rbt_joinR :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "rbt_joinR l x r = (if bheight l \<le> bheight r then MR l x r
    else case l of MB l' x' r' \<Rightarrow> baliR l' x' (rbt_joinR r' x r)
    | MR l' x' r' \<Rightarrow> MR l' x' (rbt_joinR r' x r))"

definition rbt_join :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "rbt_join l x r = (if bheight l > bheight r
    then paint RBT_Impl.B (rbt_joinR l x r)
    else if bheight l < bheight r
    then paint RBT_Impl.B (rbt_joinL l x r)
    else MB l x r)"

declare rbt_joinL.simps[simp del]
declare rbt_joinR.simps[simp del]

lemma [simp]: "size (paint c t) = size t"
  by (cases t) auto

lemma size_baliL[simp]: "size (baliL t1 x t2) = Suc (size t1 + size t2)"
  by (induction t1 x t2 rule: baliL.induct) auto

lemma size_baliR[simp]: "size (baliR t1 x t2) = Suc (size t1 + size t2)"
  by (induction t1 x t2 rule: baliR.induct) auto

lemma size_baldL[simp]: "size (baldL t1 x t2) = Suc (size t1 + size t2)"
  by (induction t1 x t2 rule: baldL.induct) auto

lemma size_baldR[simp]: "size (baldR t1 x t2) = Suc (size t1 + size t2)"
  by (induction t1 x t2 rule: baldR.induct) auto

lemma size_app[simp]: "size (app t1 t2) = size t1 + size t2"
  by (induction t1 t2 rule: app.induct)
     (auto split: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)

lemma size_rbt_joinL[simp]: "size (rbt_joinL t1 x t2) = Suc (size t1 + size t2)"
  by (induction t1 x t2 rule: rbt_joinL.induct)
     (auto simp: rbt_joinL.simps split: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)

lemma size_rbt_joinR[simp]: "size (rbt_joinR t1 x t2) = Suc (size t1 + size t2)"
  by (induction t1 x t2 rule: rbt_joinR.induct)
     (auto simp: rbt_joinR.simps split: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)

lemma size_rbt_join[simp]: "size (rbt_join t1 x t2) = Suc (size t1 + size t2)"
  by (auto simp: rbt_join_def)

definition "rbt t \<longleftrightarrow> inv1 t \<and> inv2 t"

lemma rbt_Node: "\<lbrakk> rbt (RBT_Impl.Branch c l a () r) \<rbrakk> \<Longrightarrow> rbt l \<and> rbt r"
  by (auto simp: rbt_def)

lemma color_of_paint_B: "color_of (paint RBT_Impl.B t) = RBT_Impl.B"
  by (cases t) auto

lemma paint2: "paint c2 (paint c1 t) = paint c2 t"
  by (cases t) auto

lemma inv1_paint_B: "inv1l t \<Longrightarrow> inv1 (paint RBT_Impl.B t)"
  by (cases t) auto

lemma inv2_paint: "inv2 t \<Longrightarrow> inv2 (paint c t)"
  by (cases t) auto

lemma inv1_baliL:
  "\<lbrakk>inv1l l; inv1 r\<rbrakk> \<Longrightarrow> inv1 (baliL l a r)"
  by (induct l a r rule: baliL.induct) auto

lemma inv1_baliR:
  "\<lbrakk>inv1 l; inv1l r\<rbrakk> \<Longrightarrow> inv1 (baliR l a r)"
  by (induct l a r rule: baliR.induct) auto

lemma bheight_baliL:
  "bheight l = bheight r \<Longrightarrow> bheight (baliL l a r) = Suc (bheight l)"
  by (induct l a r rule: baliL.induct) auto

lemma bheight_baliR:
  "bheight l = bheight r \<Longrightarrow> bheight (baliR l a r) = Suc (bheight l)"
  by (induct l a r rule: baliR.induct) auto

lemma inv2_baliL:
  "\<lbrakk> inv2 l; inv2 r; bheight l = bheight r \<rbrakk> \<Longrightarrow> inv2 (baliL l a r)"
  by (induct l a r rule: baliL.induct) auto

lemma inv2_baliR:
  "\<lbrakk> inv2 l; inv2 r; bheight l = bheight r \<rbrakk> \<Longrightarrow> inv2 (baliR l a r)"
  by (induct l a r rule: baliR.induct) auto

lemma inv_baliR: "\<lbrakk> inv2 l; inv2 r; inv1 l; inv1l r; bheight l = bheight r \<rbrakk>
 \<Longrightarrow> inv1 (baliR l a r) \<and> inv2 (baliR l a r) \<and> bheight (baliR l a r) = Suc (bheight l)"
  by (induct l a r rule: baliR.induct) auto

lemma inv_baliL: "\<lbrakk> inv2 l; inv2 r; inv1l l; inv1 r; bheight l = bheight r \<rbrakk>
 \<Longrightarrow> inv1 (baliL l a r) \<and> inv2 (baliL l a r) \<and> bheight (baliL l a r) = Suc (bheight l)"
  by (induct l a r rule: baliL.induct) auto

lemma bheight_paint_R:
  "color_of t = RBT_Impl.B \<Longrightarrow> bheight (paint RBT_Impl.R t) = bheight t - 1"
  by (cases t) auto

lemma inv2_baldL_inv1:
  "\<lbrakk> inv2 l;  inv2 r;  bheight l + 1 = bheight r;  inv1 r \<rbrakk>
   \<Longrightarrow> inv2 (baldL l a r) \<and> bheight (baldL l a r) = bheight r"
  by (induct l a r rule: baldL.induct)
     (auto simp: inv2_baliR inv2_paint bheight_baliR bheight_paint_R)

lemma inv2_baldL_B:
  "\<lbrakk> inv2 l;  inv2 r;  bheight l + 1 = bheight r; color_of r = RBT_Impl.B \<rbrakk>
   \<Longrightarrow> inv2 (baldL l a r) \<and> bheight (baldL l a r) = bheight r"
  by (induct l a r rule: baldL.induct) (auto simp add: inv2_baliR bheight_baliR)

lemma inv1_baldL: "\<lbrakk>inv1l l; inv1 r; color_of r = RBT_Impl.B\<rbrakk> \<Longrightarrow> inv1 (baldL l a r)"
  by (induct l a r rule: baldL.induct) (simp_all add: inv1_baliR)

lemma inv1lI: "inv1 t \<Longrightarrow> inv1l t"
  by (cases t) auto

lemma neq_Black[simp]: "(c \<noteq> RBT_Impl.B) = (c = RBT_Impl.R)"
  by (cases c) auto

lemma [simp]: "inv1 t \<Longrightarrow> inv1l (paint c t)"
  by (cases t) auto

lemma inv1l_baldL: "\<lbrakk> inv1l l; inv1 r \<rbrakk> \<Longrightarrow> inv1l (baldL l a r)"
  by (induct l a r rule: baldL.induct) (auto simp: inv1_baliR paint2)

lemma inv2_baldR_inv1:
  "\<lbrakk> inv2 l;  inv2 r;  bheight l = bheight r + 1;  inv1 l \<rbrakk>
  \<Longrightarrow> inv2 (baldR l a r) \<and> bheight (baldR l a r) = bheight l"
  by (induct l a r rule: baldR.induct)
     (auto simp: inv2_baliL bheight_baliL inv2_paint bheight_paint_R)

lemma inv1_baldR: "\<lbrakk>inv1 l; inv1l r; color_of l = RBT_Impl.B\<rbrakk> \<Longrightarrow> inv1 (baldR l a r)"
  by (induct l a r rule: baldR.induct) (simp_all add: inv1_baliL)

lemma inv1l_baldR: "\<lbrakk> inv1 l; inv1l r \<rbrakk> \<Longrightarrow>inv1l (baldR l a r)"
  by (induct l a r rule: baldR.induct) (auto simp: inv1_baliL paint2)

lemma inv2_app:
  "\<lbrakk> inv2 l; inv2 r; bheight l = bheight r \<rbrakk>
  \<Longrightarrow> inv2 (app l r) \<and> bheight (app l r) = bheight l"
  by (induct l r rule: app.induct)
     (auto simp: inv2_baldL_B split: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)

lemma inv1_app:
  "\<lbrakk> inv1 l; inv1 r \<rbrakk> \<Longrightarrow>
    (color_of l = RBT_Impl.B \<and> color_of r = RBT_Impl.B \<longrightarrow> inv1 (app l r)) \<and> inv1l (app l r)"
  by (induct l r rule: app.induct)
     (auto simp: inv1_baldL split: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)

lemma inv_baldL:
  "\<lbrakk> inv2 l;  inv2 r;  bheight l + 1 = bheight r; inv1l l; inv1 r \<rbrakk>
   \<Longrightarrow> inv2 (baldL l a r) \<and> bheight (baldL l a r) = bheight r
  \<and> inv1l (baldL l a r) \<and> (color_of r = RBT_Impl.B \<longrightarrow> inv1 (baldL l a r))"
  by (induct l a r rule: baldL.induct)
     (auto simp: inv_baliR inv2_paint bheight_baliR bheight_paint_R paint2)

lemma inv_baldR:
  "\<lbrakk> inv2 l;  inv2 r;  bheight l = bheight r + 1; inv1 l; inv1l r \<rbrakk>
   \<Longrightarrow> inv2 (baldR l a r) \<and> bheight (baldR l a r) = bheight l
  \<and> inv1l (baldR l a r) \<and> (color_of l = RBT_Impl.B \<longrightarrow> inv1 (baldR l a r))"
  by (induct l a r rule: baldR.induct)
     (auto simp: inv_baliL inv2_paint bheight_baliL bheight_paint_R paint2)

lemma inv_app:
  "\<lbrakk> inv2 l; inv2 r; bheight l = bheight r; inv1 l; inv1 r \<rbrakk>
  \<Longrightarrow> inv2 (app l r) \<and> bheight (app l r) = bheight l
  \<and> inv1l (app l r) \<and> (color_of l = RBT_Impl.B \<and> color_of r = RBT_Impl.B \<longrightarrow> inv1 (app l r))"
  by (induct l r rule: app.induct)
     (auto simp: inv2_baldL_B inv_baldL
      split: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)

lemma neq_LeafD: "t \<noteq> RBT_Impl.Empty \<Longrightarrow> \<exists>l x c r. t = RBT_Impl.Branch c l x () r"
  by (cases t) auto

lemma inv1l_rbt_joinL:
 "\<lbrakk> inv1 l; inv1 r; bheight l \<le> bheight r \<rbrakk> \<Longrightarrow>
  inv1l (rbt_joinL l x r)
  \<and> (bheight l \<noteq> bheight r \<and> color_of r = RBT_Impl.B \<longrightarrow> inv1(rbt_joinL l x r))"
proof (induct l x r rule: rbt_joinL.induct)
  case (1 l x r) thus ?case
    by (auto simp: inv1_baliL rbt_joinL.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma inv1l_rbt_joinR:
  "\<lbrakk> inv1 l; inv2 l; inv1 r; inv2 r; bheight l \<ge> bheight r \<rbrakk> \<Longrightarrow>
  inv1l (rbt_joinR l x r)
  \<and> (bheight l \<noteq> bheight r \<and> color_of l = RBT_Impl.B \<longrightarrow> inv1(rbt_joinR l x r))"
proof (induct l x r rule: rbt_joinR.induct)
  case (1 l x r) thus ?case
    by (fastforce simp: inv1_baliR rbt_joinR.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma bheight_rbt_joinL:
  "\<lbrakk> inv2 l; inv2 r; bheight l \<le> bheight r \<rbrakk> \<Longrightarrow> bheight (rbt_joinL l x r) = bheight r"
proof (induct l x r rule: rbt_joinL.induct)
  case (1 l x r) thus ?case
    by (auto simp: bheight_baliL rbt_joinL.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma inv2_rbt_joinL:
  "\<lbrakk> inv2 l;  inv2 r;  bheight l \<le> bheight r \<rbrakk> \<Longrightarrow> inv2 (rbt_joinL l x r)"
proof (induct l x r rule: rbt_joinL.induct)
  case (1 l x r) thus ?case
    by (auto simp: inv2_baliL bheight_rbt_joinL rbt_joinL.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma bheight_rbt_joinR:
  "\<lbrakk> inv2 l;  inv2 r;  bheight l \<ge> bheight r \<rbrakk> \<Longrightarrow> bheight (rbt_joinR l x r) = bheight l"
proof (induct l x r rule: rbt_joinR.induct)
  case (1 l x r) thus ?case
    by (fastforce simp: bheight_baliR rbt_joinR.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma inv2_rbt_joinR:
  "\<lbrakk> inv2 l; inv2 r; bheight l \<ge> bheight r \<rbrakk> \<Longrightarrow> inv2 (rbt_joinR l x r)"
proof (induct l x r rule: rbt_joinR.induct)
  case (1 l x r) thus ?case
    by (fastforce simp: inv2_baliR bheight_rbt_joinR rbt_joinR.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma bheight_paint_Black: "bheight (paint RBT_Impl.B t) \<le> bheight t + 1"
  by (cases t) auto

lemma keys_paint: "RBT_Impl.keys (paint c t) = RBT_Impl.keys t"
  by (cases t) auto

lemma keys_baliL:
  "RBT_Impl.keys (baliL l a r) = RBT_Impl.keys l @ a # RBT_Impl.keys r"
  by (cases "(l,a,r)" rule: baliL.cases) auto

lemma keys_baliR:
  "RBT_Impl.keys (baliR l a r) = RBT_Impl.keys l @ a # RBT_Impl.keys r"
  by (cases "(l,a,r)" rule: baliR.cases) auto

lemma keys_baldL:
  "RBT_Impl.keys (baldL l a r) = RBT_Impl.keys l @ a # RBT_Impl.keys r"
  by (cases "(l,a,r)" rule: baldL.cases)
     (auto simp: keys_baliL keys_baliR keys_paint)

lemma keys_baldR:
  "RBT_Impl.keys (baldR l a r) = RBT_Impl.keys l @ a # RBT_Impl.keys r"
  by (cases "(l,a,r)" rule: baldR.cases)
     (auto simp: keys_baliL keys_baliR keys_paint)

lemma keys_app:
  "RBT_Impl.keys (app l r) = RBT_Impl.keys l @ RBT_Impl.keys r"
  by (induction l r rule: app.induct)
     (auto simp: keys_baldL keys_baldR
      split: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)

lemma keys_rbt_joinL: "bheight l \<le> bheight r \<Longrightarrow>
  RBT_Impl.keys (rbt_joinL l x r) = RBT_Impl.keys l @ x # RBT_Impl.keys r"
proof (induction l x r rule: rbt_joinL.induct)
  case (1 l x r)
  thus ?case
    by (auto simp: keys_baliL rbt_joinL.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma keys_rbt_joinR:
  "RBT_Impl.keys (rbt_joinR l x r) = RBT_Impl.keys l @ x # RBT_Impl.keys r"
proof (induction l x r rule: rbt_joinR.induct)
  case (1 l x r)
  thus ?case
    by (force simp: keys_baliR rbt_joinR.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma set_baliL:
  "set (RBT_Impl.keys (baliL l a r)) = set (RBT_Impl.keys l) \<union> {a} \<union> set (RBT_Impl.keys r)"
  by (cases "(l,a,r)" rule: baliL.cases) auto

lemma set_rbt_joinL:
  "bheight l \<le> bheight r \<Longrightarrow>
  set (RBT_Impl.keys (rbt_joinL l x r)) = set (RBT_Impl.keys l) \<union> {x} \<union> set (RBT_Impl.keys r)"
proof (induction l x r rule: rbt_joinL.induct)
  case (1 l x r)
  thus ?case
    by (auto simp: set_baliL rbt_joinL.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma set_baliR:
  "set (RBT_Impl.keys (baliR l a r)) = set (RBT_Impl.keys l) \<union> {a} \<union> set (RBT_Impl.keys r)"
  by (cases "(l,a,r)" rule: baliR.cases) auto

lemma set_rbt_joinR:
  "set (RBT_Impl.keys (rbt_joinR l x r)) = set (RBT_Impl.keys l) \<union> {x} \<union> set (RBT_Impl.keys r)"
proof (induction l x r rule: rbt_joinR.induct)
  case (1 l x r)
  thus ?case
    by (force simp: set_baliR rbt_joinR.simps[of l x r]
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma set_paint: "set (RBT_Impl.keys (paint c t)) = set (RBT_Impl.keys t)"
  by (cases t) auto

lemma set_rbt_join: "set (RBT_Impl.keys (rbt_join l x r)) =
  set (RBT_Impl.keys l) \<union> {x} \<union> set (RBT_Impl.keys r)"
  by (simp add: set_rbt_joinL set_rbt_joinR set_paint rbt_join_def)

lemma inv_rbt_join: "\<lbrakk> inv1 l; inv2 l; inv1 r; inv2 r \<rbrakk> \<Longrightarrow>
  inv1 (rbt_join l x r) \<and> inv2 (rbt_join l x r)"
  by (auto simp: rbt_join_def inv1l_rbt_joinL inv1l_rbt_joinR inv2_rbt_joinL inv2_rbt_joinR
      inv2_paint inv1_paint_B)

lemma color_of_rbt_join: "color_of (rbt_join l x r) = color.B"
  by (auto simp: rbt_join_def color_of_paint_B)

lemma rbt_join: "rbt l \<Longrightarrow> rbt r \<Longrightarrow> rbt (rbt_join l x r)"
  using inv_rbt_join
  by (fastforce simp: rbt_def color_of_rbt_join)

fun rbt_recolor :: "('a, unit) rbt \<Rightarrow> ('a, unit) rbt" where
  "rbt_recolor (Branch RBT_Impl.R t1 k v t2) =
    (if color_of t1 = RBT_Impl.B \<and> color_of t2 = RBT_Impl.B then Branch RBT_Impl.B t1 k v t2
    else Branch RBT_Impl.R t1 k v t2)"
| "rbt_recolor t = t"

lemma rbt_recolor: "rbt t \<Longrightarrow> rbt (rbt_recolor t)"
  by (induction t rule: rbt_recolor.induct) (auto simp: rbt_def)

fun split_min :: "'a urbt \<Rightarrow> 'a \<times> 'a urbt" where
  "split_min RBT_Impl.Empty = undefined"
| "split_min (RBT_Impl.Branch _ l a _ r) =
    (if is_empty l then (a,r) else let (m, l') = split_min l in (m, rbt_join l' a r))"

lemma split_min_set:
  "\<lbrakk> split_min t = (m,t');  t \<noteq> RBT_Impl.Empty \<rbrakk> \<Longrightarrow>
  m \<in> set (RBT_Impl.keys t) \<and> set (RBT_Impl.keys t) = {m} \<union> set (RBT_Impl.keys t')"
  by (induction t arbitrary: t') (auto simp: set_rbt_join split: prod.splits if_splits)

lemma split_min_inv:
  "\<lbrakk> split_min t = (m,t');  rbt t;  t \<noteq> RBT_Impl.Empty \<rbrakk> \<Longrightarrow> rbt t'"
  by (induction t arbitrary: t') (auto simp: rbt_join split: if_splits prod.splits dest: rbt_Node)

definition rbt_join2 :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "rbt_join2 l r = (if is_empty r then l else let (m, r') = split_min r in rbt_join l m r')"

lemma set_rbt_join2[simp]:
  "set (RBT_Impl.keys (rbt_join2 l r)) = set (RBT_Impl.keys l) \<union> set (RBT_Impl.keys r)"
  by (simp add: rbt_join2_def split_min_set set_rbt_join split: prod.split)

lemma inv_rbt_join2: "\<lbrakk> rbt l; rbt r \<rbrakk> \<Longrightarrow> rbt (rbt_join2 l r)"
  by (simp add: rbt_join2_def rbt_join inv_rbt_join split_min_set split_min_inv split: prod.split)

context ord begin

fun split :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<times> bool \<times> 'a urbt" where
  "split RBT_Impl.Empty k = (RBT_Impl.Empty, False, RBT_Impl.Empty)"
| "split (RBT_Impl.Branch _ l a () r) x =
  (if x < a then (case split l x of (l1, b, l2) \<Rightarrow> (l1, b, rbt_join l2 a r))
  else if a < x then (case split r x of (r1, b, r2) \<Rightarrow> (rbt_join l a r1, b, r2))
  else (l, True, r))"

lemma split_rbt: "split t x = (l,xin,r) \<Longrightarrow> rbt t \<Longrightarrow> rbt l \<and> rbt r"
  by (induction t arbitrary: l xin r)
     (auto simp: set_rbt_join rbt_join rbt_greater_prop rbt_less_prop
      split: if_splits prod.splits dest!: rbt_Node)

lemma split_size: "split t2 a = (l2, b, r2) \<Longrightarrow> size l2 + size r2 \<le> size t2"
  by (induction t2 a arbitrary: l2 b r2 rule: split.induct) (auto split: if_splits prod.splits)

function union :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "union t1 t2 = (let (t1, t2) = if flip_rbt t1 t2 then (t2, t1) else (t1, t2) in
    if small_rbt t1 then RBT_Impl.fold rbt_insert t1 t2
    else (case t2 of RBT_Impl.Empty \<Rightarrow> t1
      | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
        case split t1 a of (l1, _, r1) \<Rightarrow> rbt_join (union l1 l2) a (union r1 r2)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(t1, t2). size t1 + size t2)")
    apply (auto split: if_splits)
     apply (metis add_leD1 le_imp_less_Suc ord.split_size trans_le_add2)
    apply (metis add_leD1 le_imp_less_Suc ord.split_size trans_le_add1)
   apply (metis add_leD2 le_imp_less_Suc ord.split_size trans_le_add2)
  apply (metis add_leD2 le_imp_less_Suc ord.split_size trans_le_add1)
  done

declare union.simps[simp del]

lemma rbt_fold_rbt_insert:
  assumes "rbt t2"
  shows "rbt (RBT_Impl.fold rbt_insert t1 t2)"
proof -
  define xs where "xs = RBT_Impl.entries t1"
  from assms show ?thesis
    unfolding RBT_Impl.fold_def xs_def[symmetric]
    by (induct xs rule: rev_induct)
       (auto simp: rbt_def rbt_insert_def rbt_insert_with_key_def ins_inv1_inv2)
qed

lemma rbt_union: "rbt t1 \<Longrightarrow> rbt t2 \<Longrightarrow> rbt (union t1 t2)"
proof (induction t1 t2 rule: union.induct)
  case (1 t1 t2)
  thus ?case
    by (auto simp: union.simps[of t1 t2] rbt_join split_rbt rbt_fold_rbt_insert
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits prod.split if_splits
        dest: rbt_Node)
qed

function inter :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "inter t1 t2 = (let (t1, t2) = if flip_rbt t1 t2 then (t2, t1) else (t1, t2) in
    if small_rbt t1 then
      rbtreeify (filter (\<lambda>(k, _). rbt_lookup t2 k = Some ()) (RBT_Impl.entries t1))
    else case t2 of RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
    | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
      case split t1 a of (l1, ain, r1) \<Rightarrow> let l' = inter l1 l2; r' = inter r1 r2
      in if ain then rbt_join l' a r' else rbt_join2 l' r')"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(t1, t2). size t1 + size t2)")
    apply (auto split: if_splits)
     apply (metis add_leD1 le_imp_less_Suc ord.split_size trans_le_add2)
    apply (metis add_leD1 le_imp_less_Suc ord.split_size trans_le_add1)
   apply (metis add_leD2 le_imp_less_Suc ord.split_size trans_le_add2)
  apply (metis add_leD2 le_imp_less_Suc ord.split_size trans_le_add1)
  done

declare inter.simps[simp del]

lemma rbt_rbtreeify[simp]: "rbt (rbtreeify kvs)"
  by (simp add: rbt_def rbtreeify_def inv1_rbtreeify_g inv2_rbtreeify_g)

lemma rbt_inter: "rbt t1 \<Longrightarrow> rbt t2 \<Longrightarrow> rbt (inter t1 t2)"
proof(induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  thus ?case
    by (auto simp: inter.simps[of t1 t2] inv_rbt_join inv_rbt_join2 split_rbt Let_def rbt_join
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits prod.split if_splits
        dest!: rbt_Node)
qed

fun minus :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "minus t1 t2 = (if small_rbt t2 then RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t2 t1
    else if small_rbt t1 then
      rbtreeify (filter (\<lambda>(k, _). rbt_lookup t2 k = None) (RBT_Impl.entries t1))
    else case t2 of RBT_Impl.Empty \<Rightarrow> t1
      | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
        case split t1 a of (l1, _, r1) \<Rightarrow> rbt_join2 (minus l1 l2) (minus r1 r2))"

declare minus.simps[simp del]

end

context linorder begin

lemma rbt_delete: "rbt t \<Longrightarrow> rbt (rbt_delete x t)"
  using rbt_del_inv1_inv2[of t x]
  by (auto simp: rbt_def rbt_delete_def rbt_del_inv1_inv2)

lemma rbt_fold_rbt_delete:
  assumes "rbt t2"
  shows "rbt (RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t1 t2)"
proof -
  define xs where "xs = RBT_Impl.entries t1"
  from assms show ?thesis
    unfolding RBT_Impl.fold_def xs_def[symmetric]
    by (induct xs rule: rev_induct) (auto simp: rbt_delete)
qed

lemma rbt_minus: "rbt t1 \<Longrightarrow> rbt t2 \<Longrightarrow> rbt (minus t1 t2)"
proof(induction t1 t2 rule: minus.induct)
  case (1 t1 t2)
  thus ?case
    by (auto simp: minus.simps[of t1 t2] inv_rbt_join inv_rbt_join2 split_rbt rbt_fold_rbt_delete
        split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits prod.split if_splits
        dest: rbt_Node)
qed

end

context
  fixes comp :: "'a comparator"
begin

fun split_comp :: "'a urbt \<Rightarrow> 'a \<Rightarrow> 'a urbt \<times> bool \<times> 'a urbt" where
  "split_comp RBT_Impl.Empty k = (RBT_Impl.Empty, False, RBT_Impl.Empty)"
| "split_comp (RBT_Impl.Branch _ l a () r) x = (case comp x a of
    Lt \<Rightarrow> (let (l1,b,l2) = split_comp l x in (l1, b, rbt_join l2 a r))
  | Gt \<Rightarrow> (let (r1,b,r2) = split_comp r x in (rbt_join l a r1, b, r2))
  | Eq \<Rightarrow> (l, True, r))"

lemma split_comp_size: "split_comp t2 a = (l2, b, r2) \<Longrightarrow> size l2 + size r2 \<le> size t2"
  by (induction t2 a arbitrary: l2 b r2 rule: split_comp.induct)
     (auto split: order.splits if_splits prod.splits)

function union_comp :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "union_comp t1 t2 = (let (t1, t2) = if flip_rbt t1 t2 then (t2, t1) else (t1, t2) in
    if small_rbt t1 then RBT_Impl.fold (rbt_comp_insert comp) t1 t2
    else (case t2 of RBT_Impl.Empty \<Rightarrow> t1
      | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
        case split_comp t1 a of (l1, _, r1) \<Rightarrow> rbt_join (union_comp l1 l2) a (union_comp r1 r2)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(t1, t2). size t1 + size t2)")
    apply (auto split: if_splits)
     apply (metis add_leD1 le_imp_less_Suc split_comp_size trans_le_add2)
    apply (metis add_leD1 le_imp_less_Suc split_comp_size trans_le_add1)
   apply (metis add_leD2 le_imp_less_Suc split_comp_size trans_le_add2)
  apply (metis add_leD2 le_imp_less_Suc split_comp_size trans_le_add1)
  done

declare union_comp.simps[simp del]

function inter_comp :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "inter_comp t1 t2 = (let (t1, t2) = if flip_rbt t1 t2 then (t2, t1) else (t1, t2) in
    if small_rbt t1 then
      rbtreeify (filter (\<lambda>(k, _). rbt_comp_lookup comp t2 k = Some ()) (RBT_Impl.entries t1))
    else case t2 of RBT_Impl.Empty \<Rightarrow> RBT_Impl.Empty
    | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
      case split_comp t1 a of (l1, ain, r1) \<Rightarrow> let l' = inter_comp l1 l2; r' = inter_comp r1 r2
      in if ain then rbt_join l' a r' else rbt_join2 l' r')"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(t1, t2). size t1 + size t2)")
    apply (auto split: if_splits)
     apply (metis add_leD1 le_imp_less_Suc split_comp_size trans_le_add2)
    apply (metis add_leD1 le_imp_less_Suc split_comp_size trans_le_add1)
   apply (metis add_leD2 le_imp_less_Suc split_comp_size trans_le_add2)
  apply (metis add_leD2 le_imp_less_Suc split_comp_size trans_le_add1)
  done

declare inter_comp.simps[simp del]

fun minus_comp :: "'a urbt \<Rightarrow> 'a urbt \<Rightarrow> 'a urbt" where
  "minus_comp t1 t2 = (if small_rbt t2 then RBT_Impl.fold (\<lambda>k _ t. rbt_comp_delete comp k t) t2 t1
    else if small_rbt t1 then
      rbtreeify (filter (\<lambda>(k, _). rbt_comp_lookup comp t2 k = None) (RBT_Impl.entries t1))
    else case t2 of RBT_Impl.Empty \<Rightarrow> t1
      | RBT_Impl.Branch _ l2 a () r2 \<Rightarrow>
        case split_comp t1 a of (l1, _, r1) \<Rightarrow> rbt_join2 (minus_comp l1 l2) (minus_comp r1 r2))"

declare minus_comp.simps[simp del]

end

context fixes c :: "'a comparator"
  assumes c: "comparator c"
begin

declare comparator.le_lt_convs[OF c, simp add]

lemma anti_sym: "lt_of_comp c a x \<Longrightarrow> lt_of_comp c x a \<Longrightarrow> False"
  by (metis c comparator.Gt_lt_conv comparator.Lt_lt_conv order.distinct(5))

lemma split_comp: "split_comp c t x = ord.split (lt_of_comp c) t x"
  by (induction t x rule: split_comp.induct[where comp=c])
     (auto simp: ord.split.simps split: order.splits prod.splits dest: anti_sym)

lemma union_comp: "union_comp c t1 t2 = ord.union (lt_of_comp c) t1 t2"
proof (induction t1 t2 rule: union_comp.induct[where comp=c])
  case (1 t1 t2)
  obtain t1' t2' where flip:
    "(t1', t2') = (if flip_rbt t1 t2 then (t2, t1) else (t1, t2))"
    by fastforce
  show ?case
  proof (cases t2')
    case (Branch _ l2 a u r2)
    have t1_not_Empty: "t2' \<noteq> RBT_Impl.Empty"
      by (auto simp: Branch)
    have u_def: "u = ()"
      by auto
    obtain l1 b r1 where split: "split_comp c t1' a = (l1, b, r1)"
      by (cases "split_comp c t1' a") auto
    show ?thesis
      using 1[OF flip refl _ Branch]
      unfolding union_comp.simps[of _ t1] ord.union.simps[of _ t1] flip[symmetric]
      by (auto simp: Branch split split_comp[symmetric] rbt_comp_insert[OF c]
          split: unit.splits prod.splits)
  qed (auto simp: union_comp.simps[of _ t1] ord.union.simps[of _ t1] flip[symmetric]
       rbt_comp_insert[OF c] split_comp[symmetric])
qed

lemma inter_comp: "inter_comp c t1 t2 = ord.inter (lt_of_comp c) t1 t2"
proof (induction t1 t2 rule: inter_comp.induct[where comp=c])
  case (1 t1 t2)
  obtain t1' t2' where flip:
    "(t1', t2') = (if flip_rbt t1 t2 then (t2, t1) else (t1, t2))"
    by fastforce
  show ?case
  proof (cases t2')
    case (Branch _ l2 a u r2)
    have t1_not_Empty: "t2' \<noteq> RBT_Impl.Empty"
      by (auto simp: Branch)
    have u_def: "u = ()"
      by auto
    obtain l1 b r1 where split: "split_comp c t1' a = (l1, b, r1)"
      by (cases "split_comp c t1' a") auto
    show ?thesis
      using 1[OF flip refl _ Branch]
      unfolding inter_comp.simps[of _ t1] ord.inter.simps[of _ t1] flip[symmetric]
      by (auto simp: Branch split split_comp[symmetric] rbt_comp_insert[OF c] rbt_comp_lookup[OF c]
          split: unit.splits prod.splits)
  qed (auto simp: inter_comp.simps[of _ t1] ord.inter.simps[of _ t1] flip[symmetric]
       rbt_comp_insert[OF c] rbt_comp_lookup[OF c] split_comp[symmetric])
qed

lemma minus_comp: "minus_comp c t1 t2 = ord.minus (lt_of_comp c) t1 t2"
proof (induction t1 t2 rule: minus_comp.induct[where comp=c])
  case (1 t1 t2)
  show ?case
  proof (cases t2)
    case (Branch _ l2 a u r2)
    have t2_not_Empty: "t2 \<noteq> RBT_Impl.Empty"
      by (auto simp: Branch)
    have u_def: "u = ()"
      by auto
    obtain l1 b r1 where split: "split_comp c t1 a = (l1, b, r1)"
      by (cases "split_comp c t1 a") auto
    show ?thesis
      using 1[OF _ _ Branch]
      unfolding minus_comp.simps[of _ t1 t2] ord.minus.simps[of _ t1 t2]
      by (auto simp: Branch split split_comp[symmetric] rbt_comp_delete[OF c] rbt_comp_lookup[OF c]
          split: unit.splits prod.splits)
  qed (auto simp: minus_comp.simps[of _ t1] ord.minus.simps[of _ t1]
       rbt_comp_delete[OF c] rbt_comp_lookup[OF c] split_comp[symmetric])
qed

end

context linorder begin

lemma rbt_sorted_baliL:
  "\<lbrakk>rbt_sorted l; rbt_sorted r; l |\<guillemotleft> a; a \<guillemotleft>| r\<rbrakk> \<Longrightarrow> rbt_sorted (baliL l a r)"
  using rbt_greater_trans rbt_less_trans
  apply (cases "(l,a,r)" rule: baliL.cases)
            apply (auto simp: rbt_sorted_def)
   apply blast+
  done

lemma rbt_sorted_baliR:
  "\<lbrakk>rbt_sorted l; rbt_sorted r; l |\<guillemotleft> a; a \<guillemotleft>| r\<rbrakk> \<Longrightarrow> rbt_sorted (baliR l a r)"
  using rbt_greater_trans rbt_less_trans
  apply (cases "(l,a,r)" rule: baliR.cases)
            apply (auto simp: rbt_sorted_def)
    apply blast+
  done

lemma rbt_sorted_rbt_joinL:
  "\<lbrakk>rbt_sorted (RBT_Impl.Branch c l a () r); bheight l \<le> bheight r\<rbrakk>
  \<Longrightarrow> rbt_sorted (rbt_joinL l a r)"
proof (induction l a r arbitrary: c rule: rbt_joinL.induct)
  case (1 l a r)
  thus ?case
    by (auto simp: set_baliL rbt_joinL.simps[of l a r] set_rbt_joinL rbt_less_prop
        intro!: rbt_sorted_baliL split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma rbt_sorted_rbt_joinR:
  "\<lbrakk>rbt_sorted l; rbt_sorted r; l |\<guillemotleft> a; a \<guillemotleft>| r\<rbrakk>
  \<Longrightarrow> rbt_sorted (rbt_joinR l a r)"
proof (induction l a r rule: rbt_joinR.induct)
  case (1 l a r)
  thus ?case
    by (auto simp: set_baliR rbt_joinR.simps[of l a r] set_rbt_joinR rbt_greater_prop
        intro!: rbt_sorted_baliR split!: RBT_Impl.rbt.splits RBT_Impl.color.splits unit.splits)
qed

lemma rbt_sorted_paint: "rbt_sorted (paint c t) = rbt_sorted t"
  by (cases t) auto

lemma rbt_sorted_rbt_join: "rbt_sorted (RBT_Impl.Branch c l a () r) \<Longrightarrow>
  rbt_sorted (rbt_join l a r)"
  by (auto simp: rbt_sorted_paint rbt_sorted_rbt_joinL rbt_sorted_rbt_joinR rbt_join_def)

lemma split_min_rbt_sorted:
  "\<lbrakk> split_min t = (m,t');  rbt_sorted t;  t \<noteq> RBT_Impl.Empty \<rbrakk> \<Longrightarrow>
  rbt_sorted t' \<and> (\<forall>x \<in> set (RBT_Impl.keys t'). m < x)"
  by (induction t arbitrary: t')
     (fastforce simp: split_min_set rbt_sorted_rbt_join set_rbt_join rbt_less_prop rbt_greater_prop
      split: if_splits prod.splits)+

lemma rbt_sorted_rbt_join2:
  "\<lbrakk> rbt_sorted l; rbt_sorted r; \<forall>x \<in> set (RBT_Impl.keys l). \<forall>y \<in> set (RBT_Impl.keys r). x < y \<rbrakk>
  \<Longrightarrow> rbt_sorted (rbt_join2 l r)"
  by (simp add: rbt_join2_def rbt_sorted_rbt_join split_min_set split_min_rbt_sorted set_rbt_join
      rbt_greater_prop rbt_less_prop split: prod.split)

lemma split: "split t x = (l,xin,r) \<Longrightarrow> rbt_sorted t \<Longrightarrow>
  set (RBT_Impl.keys l) = {a \<in> set (RBT_Impl.keys t). a < x} \<and>
  set (RBT_Impl.keys r) = {a \<in> set (RBT_Impl.keys t). x < a} \<and>
  (xin = (x \<in> set (RBT_Impl.keys t))) \<and> rbt_sorted l \<and> rbt_sorted r"
  by (induction t arbitrary: l xin r)
     (force simp: Let_def set_rbt_join rbt_greater_prop rbt_less_prop
      split: if_splits prod.splits intro!: rbt_sorted_rbt_join)+

lemma keys_paint'[simp]: "RBT_Impl.keys (RBT_Impl.paint c t) = RBT_Impl.keys t"
  by (cases t) auto

lemma [simp]: "set (RBT_Impl.keys (rbt_insert x y t2)) = {x} \<union> set (RBT_Impl.keys t2)"
  by (auto simp: rbt_insert_def rbt_insert_with_key_def keys_ins)

lemma set_tree_fold_insert:
  assumes "rbt_sorted t2"
  shows "set (RBT_Impl.keys (RBT_Impl.fold rbt_insert t1 t2)) =
    set (RBT_Impl.keys t1) \<union> set (RBT_Impl.keys t2)"
proof -
  define xs where "xs = RBT_Impl.entries t1"
  have keys_t1: "set (RBT_Impl.keys t1) = fst ` set xs"
    by (auto simp: xs_def RBT_Impl.keys_def)
  from assms show ?thesis
    unfolding RBT_Impl.fold_def xs_def[symmetric] keys_t1
    by (induct xs rule: rev_induct) (auto simp: rev_image_eqI)
qed

lemma rbt_sorted_union: "rbt_sorted t1 \<Longrightarrow> rbt_sorted t2 \<Longrightarrow>
  set (RBT_Impl.keys (union t1 t2)) = set (RBT_Impl.keys t1) \<union> set (RBT_Impl.keys t2) \<and>
  rbt_sorted (union t1 t2)"
proof(induction t1 t2 rule: union.induct)
  case (1 t1 t2)
  obtain t1' t2' where flip:
    "(t1', t2') = (if flip_rbt t1 t2 then (t2, t1) else (t1, t2))"
    by fastforce
  have set_flip: "set (RBT_Impl.keys t1) \<union> set (RBT_Impl.keys t2) =
      set (RBT_Impl.keys t1') \<union> set (RBT_Impl.keys t2')"
    using flip
    by (auto split: if_splits)
  have rbt_sorted': "rbt_sorted t1'" "rbt_sorted t2'"
    using 1(3,4) flip
    by (auto split: if_splits)
  then show ?case
  proof (cases t2')
    case (Branch _ l2 a u r2)
    obtain l1 b r1 where split_t1': "split t1' a = (l1, b, r1)"
      by (cases "split t1' a") auto
    have rbt_sort: "rbt_sorted l2" "rbt_sorted r2"
      using 1(3,4) flip
      by (auto simp: Branch split: if_splits)
    note split_t1'_prop = split[OF split_t1' rbt_sorted'(1)]
    have union_l1_l2: "\<not>small_rbt t1' \<Longrightarrow>
      set (RBT_Impl.keys (union l1 l2)) = set (RBT_Impl.keys l1) \<union> set (RBT_Impl.keys l2) \<and>
      rbt_sorted (union l1 l2)"
      using 1(1)[OF flip _ _ Branch _ split_t1'[symmetric]] rbt_sort split_t1'_prop
      by auto
    have union_r1_r2: "\<not>small_rbt t1' \<Longrightarrow>
      set (RBT_Impl.keys (union r1 r2)) = set (RBT_Impl.keys r1) \<union> set (RBT_Impl.keys r2) \<and>
      rbt_sorted (union r1 r2)"
      using 1(2)[OF flip _ _ Branch _ split_t1'[symmetric]] rbt_sort split_t1'_prop
      by auto
    have "set (RBT_Impl.keys (union t1 t2)) = set (RBT_Impl.keys t1) \<union> set (RBT_Impl.keys t2)"
      using rbt_sorted' union_l1_l2 union_r1_r2 split_t1'_prop
      unfolding set_flip
      by (auto 0 0 simp: union.simps[of t1] flip[symmetric] set_tree_fold_insert)
         (auto simp: Branch split_t1' set_rbt_join split!: unit.splits if_splits)
    moreover have "rbt_sorted (union t1 t2)"
      using rbt_sorted' 1(3,4) union_l1_l2 union_r1_r2 split_t1'_prop
      by (auto 0 0 simp: union.simps[of t1] flip[symmetric] rbt_sorted_fold_insert)
         (auto simp: Branch split_t1' rbt_less_prop rbt_greater_prop intro!: rbt_sorted_rbt_join
          split!: unit.splits if_splits)
    ultimately show ?thesis
      by auto
  qed (auto simp: set_flip union.simps[of t1] flip[symmetric] set_tree_fold_insert
       intro!: rbt_sorted_fold_insert)
qed

lemma rbt_sorted_rbtreeify:
  "rbt_sorted t \<Longrightarrow> rbt_sorted (rbtreeify (filter P (RBT_Impl.entries t)))"
  using distinct_map_filterI distinct_entries rbt_sorted_entries rbt_sorted_rbtreeify sorted_filter
  by blast

lemma rbtreeify_keys_Some:
  assumes "rbt_sorted t1"
  shows "set (RBT_Impl.keys (rbtreeify (filter (\<lambda>(k, _). rbt_lookup t1 k = Some ())
  (RBT_Impl.entries t2)))) = set (RBT_Impl.keys t1) \<inter> set (RBT_Impl.keys t2)"
  apply (auto simp: RBT_Impl.keys_def map_of_entries[OF assms, symmetric])
   apply (metis map_of_eq_None_iff not_None_eq)
  using image_iff weak_map_of_SomeI
  apply fastforce
  done

lemma rbt_sorted_inter: "rbt_sorted t1 \<Longrightarrow> rbt_sorted t2 \<Longrightarrow>
  set (RBT_Impl.keys (inter t1 t2)) = set (RBT_Impl.keys t1) \<inter> set (RBT_Impl.keys t2) \<and>
  rbt_sorted (inter t1 t2)"
proof(induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  obtain t1' t2' where flip:
    "(t1', t2') = (if flip_rbt t1 t2 then (t2, t1) else (t1, t2))"
    by fastforce
  have set_flip: "set (RBT_Impl.keys t1) \<inter> set (RBT_Impl.keys t2) =
    set (RBT_Impl.keys t1') \<inter> set (RBT_Impl.keys t2')"
    using flip
    by (auto split: if_splits)
  have rbt_sorted': "rbt_sorted t1'" "rbt_sorted t2'"
    using 1(3,4) flip
    by (auto split: if_splits)
  show ?case
  proof (cases t2')
    case [simp]: (Branch _ l2 a u r2)
    have set_flip: "set (RBT_Impl.keys t1) \<inter> set (RBT_Impl.keys t2) =
      set (RBT_Impl.keys t1') \<inter> set (RBT_Impl.keys t2')"
      using flip
      by (auto split: if_splits)
    obtain l1 b r1 where sp: "split t1' a = (l1, b, r1)"
      by (cases "split t1' a") auto
    have rbt_sort: "rbt_sorted l2" "rbt_sorted r2"
      using 1(3,4) flip
      by (auto split: if_splits)
    note split_t1'_prop = split[OF sp rbt_sorted'(1)]
    have inter_l1_l2: "\<not>small_rbt t1' \<Longrightarrow>
      set (RBT_Impl.keys (inter l1 l2)) = set (RBT_Impl.keys l1) \<inter> set (RBT_Impl.keys l2) \<and>
      rbt_sorted (inter l1 l2)"
      using 1(1)[OF flip _ _ Branch _ sp[symmetric]] rbt_sort split_t1'_prop
      by auto
    have inter_r1_r2: "\<not>small_rbt t1' \<Longrightarrow>
      set (RBT_Impl.keys (inter r1 r2)) = set (RBT_Impl.keys r1) \<inter> set (RBT_Impl.keys r2) \<and>
      rbt_sorted (inter r1 r2)"
      using 1(2)[OF flip _ _ Branch _ sp[symmetric]] rbt_sort split_t1'_prop
      by auto
    {
      assume not_small: "\<not>small_rbt t1'"
      let ?L2 = "set (RBT_Impl.keys l2)"
      let ?R2 = "set (RBT_Impl.keys r2)"
      have *: "a \<notin> ?L2 \<union> ?R2" using \<open>rbt_sorted t2'\<close>
        by (auto simp: rbt_less_prop rbt_greater_prop)
      let ?L1 = "set (RBT_Impl.keys l1)"
      let ?R1 = "set (RBT_Impl.keys r1)"
      let ?K = "if b then {a} else {}"
      have t2: "set (RBT_Impl.keys t1') = ?L1 \<union> ?R1 \<union> ?K" and
        **: "?L1 \<inter> ?R1 = {}" "a \<notin> ?L1 \<union> ?R1" "?L2 \<inter> ?R1 = {}" "?L1 \<inter> ?R2 = {}"
        using split[OF sp] less_linear \<open>rbt_sorted t1'\<close> \<open>rbt_sorted t2'\<close>
        by (auto simp: rbt_less_prop rbt_greater_prop)
      have "set (RBT_Impl.keys t1') \<inter> set (RBT_Impl.keys t2') =
        (?L2 \<union> ?R2 \<union> {a}) \<inter> (?L1 \<union> ?R1 \<union> ?K)"
        by (auto simp add: t2)
      also have "\<dots> = (?L1 \<inter> ?L2) \<union> (?R1 \<inter> ?R2) \<union> ?K"
        using * ** by auto
      also have "\<dots> = set (RBT_Impl.keys (inter t1 t2))"
        using inter_l1_l2[OF not_small] inter_r1_r2[OF not_small]
        by (auto simp: inter.simps[of t1] flip[symmetric] not_small sp set_rbt_join
            split: unit.splits)
      finally have "set (RBT_Impl.keys (inter t1 t2)) =
      set (RBT_Impl.keys t1) \<inter> set (RBT_Impl.keys t2)"
        unfolding set_flip
        by auto
    }
    moreover have "small_rbt t1' \<Longrightarrow> set (RBT_Impl.keys (inter t1 t2)) =
      set (RBT_Impl.keys (rbtreeify (filter (\<lambda>(k, _). rbt_lookup t2' k = Some ())
      (RBT_Impl.entries t1'))))"
      by (auto simp: inter.simps[of t1] flip[symmetric])
    ultimately have "set (RBT_Impl.keys (ord_class.inter t1 t2)) =
      set (RBT_Impl.keys t1) \<inter> set (RBT_Impl.keys t2)"
      using flip
      unfolding rbtreeify_keys_Some[OF rbt_sorted'(2)] set_flip
      by auto
    moreover have "rbt_sorted (inter t1 t2)"
      using rbt_sorted'(1) rbt_sort 1(3,4) inter_l1_l2 inter_r1_r2 split_t1'_prop
      by (auto 0 0 simp: inter.simps[of t1] flip[symmetric] sp rbt_less_prop rbt_greater_prop
          intro!: rbt_sorted_rbtreeify rbt_sorted_rbt_join rbt_sorted_rbt_join2
          split!: unit.splits if_splits)
         (meson local.order.strict_trans)
    ultimately show ?thesis
      by auto
  qed (auto simp: rbtreeify_def set_flip inter.simps[of t1] flip[symmetric])
qed

lemma [simp]: "RBT_Impl.entries (RBT_Impl.paint c t) = RBT_Impl.entries t"
  by (cases t) auto

lemma [simp]: "rbt t \<Longrightarrow> rbt_sorted t \<Longrightarrow>
  set (RBT_Impl.keys (rbt_delete x t)) = set (RBT_Impl.keys t) - {x}"
  using rbt_del_in_tree image_iff
  by (fastforce simp: rbt_def RBT_Impl.keys_def rbt_delete_def)

lemma [simp]: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_delete x t)"
  by (auto simp: rbt_delete_def rbt_del_rbt_sorted)

lemma fold_rbt_delete:
  assumes "rbt t2" "rbt_sorted t2"
  shows "set (RBT_Impl.keys (RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t1 t2)) =
    set (RBT_Impl.keys t2) - set (RBT_Impl.keys t1)"
    "rbt (RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t1 t2)"
    "rbt_sorted (RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t1 t2)"
proof -
  define xs where "xs = RBT_Impl.entries t1"
  have keys_t1: "set (RBT_Impl.keys t1) = fst ` set xs"
    by (auto simp: xs_def RBT_Impl.keys_def)
  from assms show
    "set (RBT_Impl.keys (RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t1 t2)) =
    set (RBT_Impl.keys t2) - set (RBT_Impl.keys t1)"
    "rbt (RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t1 t2)"
    "rbt_sorted (RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t1 t2)"
    unfolding RBT_Impl.fold_def xs_def[symmetric] keys_t1
    by (induct xs rule: rev_induct) (auto simp: rev_image_eqI rbt_delete rbt_del_rbt_sorted)
qed

lemma rbt_sorted_fold_delete: "rbt_sorted t \<Longrightarrow>
  rbt_sorted (RBT_Impl.fold (\<lambda>k _ t. rbt_delete k t) t' t)"
  by (induct t' arbitrary: t) auto

lemma rbtreeify_keys_None:
  assumes "rbt_sorted t1"
  shows "set (RBT_Impl.keys (rbtreeify (filter (\<lambda>(k, _). rbt_lookup t1 k = None)
  (RBT_Impl.entries t2)))) = set (RBT_Impl.keys t2) - set (RBT_Impl.keys t1)"
  apply (auto simp: RBT_Impl.keys_def map_of_entries[OF assms, symmetric] split: prod.splits)
  using image_iff weak_map_of_SomeI
   apply fastforce
  apply (smt fst_conv image_iff map_of_eq_None_iff mem_Collect_eq)
  done

lemma rbt_sorted_minus:
  "rbt t1 \<Longrightarrow> rbt_sorted t1 \<Longrightarrow> rbt_sorted t2 \<Longrightarrow>
  set (RBT_Impl.keys (minus t1 t2)) = set (RBT_Impl.keys t1) - set (RBT_Impl.keys t2) \<and>
  rbt_sorted (minus t1 t2)"
proof(induction t1 t2 rule: minus.induct)
  case (1 t1 t2)
  show ?case
  proof (cases t2)
    case Empty
    show ?thesis
      using 1(4,5)
      by (auto simp: minus.simps rbtreeify_keys_None intro!: rbt_sorted_rbtreeify)
         (auto simp: Empty)
  next
    case [simp]: (Branch _ l2 a _ r2)
    let ?L2 = "set (RBT_Impl.keys l2)" let ?R2 = "set (RBT_Impl.keys r2)"
    obtain l1 ain r1 where sp: "split t1 a = (l1,ain,r1)" using prod_cases3 by blast
    let ?L1 = "set (RBT_Impl.keys l1)"
    let ?R1 = "set (RBT_Impl.keys r1)"
    let ?K = "if ain then {a} else {}"
    have rbt_l1_r1: "rbt l1" "rbt r1"
      using split_rbt[OF sp 1(3)]
      by auto
    have t1: "set (RBT_Impl.keys t1) = ?L1 \<union> ?R1 \<union> ?K" and
      **: "a \<notin> ?L1 \<union> ?R1" "?L1 \<inter> ?R2 = {}" "?L2 \<inter> ?R1 = {}"
      using split[OF sp] less_linear \<open>rbt_sorted t1\<close> \<open>rbt_sorted t2\<close>
      by (auto simp: rbt_less_prop rbt_greater_prop)
    have IHl: "\<not> small_rbt t1 \<Longrightarrow> \<not>small_rbt t2 \<Longrightarrow> set (RBT_Impl.keys (minus l1 l2)) =
      set (RBT_Impl.keys l1) - set (RBT_Impl.keys l2) \<and> rbt_sorted (minus l1 l2)"
      using "1.IH"(1)[OF _ _ _ _ sp[symmetric]] "1.prems"(1,2,3) split[OF sp] rbt_l1_r1 by simp
    have IHr: "\<not> small_rbt t1 \<Longrightarrow> \<not>small_rbt t2 \<Longrightarrow> set (RBT_Impl.keys (minus r1 r2)) =
      set (RBT_Impl.keys r1) - set (RBT_Impl.keys r2) \<and> rbt_sorted (minus r1 r2)"
      using "1.IH"(2)[OF _ _ _ _ sp[symmetric]] "1.prems"(1,2,3) split[OF sp] rbt_l1_r1 by simp
    {
      assume IH: "\<not>small_rbt t1" "\<not>small_rbt t2"
      have "set (RBT_Impl.keys t1) - set (RBT_Impl.keys t2) = (?L1 \<union> ?R1) - (?L2 \<union> ?R2  \<union> {a})"
        by (simp add: t1)
      also have "\<dots> = (?L1 - ?L2) \<union> (?R1 - ?R2)"
        using ** by auto
      also have "\<dots> = set (RBT_Impl.keys (minus t1 t2))"
        using IH
        by (auto simp add: minus.simps[of t1] sp IHl IHr split: unit.splits)
      finally have
        "set (RBT_Impl.keys (minus t1 t2)) = set (RBT_Impl.keys t1) - set (RBT_Impl.keys t2)"
        by auto
    }
    then have "set (RBT_Impl.keys (ord_class.minus t1 t2)) =
      set (RBT_Impl.keys t1) - set (RBT_Impl.keys t2)"
      using 1(3,4) fold_rbt_delete
      by (auto simp add: minus.simps[of t1] sp rbtreeify_keys_None[OF 1(5)] simp del: Branch)
    moreover have "rbt_sorted (minus t1 t2)"
      using 1(3,4,5) IHl IHr split[OF sp 1(4)]
      by (auto simp: minus.simps[of t1] sp rbt_less_prop rbt_greater_prop rbt_sorted_fold_delete
          intro!: rbt_sorted_rbtreeify rbt_sorted_rbt_join rbt_sorted_rbt_join2
          split!: unit.splits if_splits)
    ultimately show ?thesis
      by auto
  qed
qed

definition is_rbt_aux :: "'a urbt \<Rightarrow> bool" where
  "is_rbt_aux t \<longleftrightarrow> inv1 t \<and> inv2 t \<and> rbt_sorted t"

lemma is_rbt_aux_prop: "is_rbt_aux t \<longleftrightarrow> rbt t \<and> rbt_sorted t"
  by (auto simp: is_rbt_aux_def rbt_def)

lemma is_rbt_prop: "is_rbt t \<longleftrightarrow> is_rbt_aux t \<and> color_of t = RBT_Impl.B"
  by (auto simp: is_rbt_def is_rbt_aux_def)

lemma is_rbt_aux_union: "\<lbrakk> is_rbt_aux t1; is_rbt_aux t2 \<rbrakk> \<Longrightarrow> is_rbt_aux (union t1 t2)"
  using rbt_sorted_union rbt_union
  by (auto simp: is_rbt_aux_prop)

lemma is_rbt_aux_inter: "\<lbrakk> is_rbt_aux t1; is_rbt_aux t2 \<rbrakk> \<Longrightarrow> is_rbt_aux (inter t1 t2)"
  using rbt_sorted_inter rbt_inter
  by (auto simp: is_rbt_aux_prop)

lemma is_rbt_aux_minus: "\<lbrakk> is_rbt_aux t1; is_rbt_aux t2 \<rbrakk> \<Longrightarrow> is_rbt_aux (minus t1 t2)"
  using rbt_sorted_minus rbt_minus
  by (auto simp: is_rbt_aux_prop)

lemma rbt_sorted_recolor: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_recolor t)"
  by (induction t rule: rbt_recolor.induct) auto

lemma color_of_rbt_recolor: "is_rbt_aux t \<Longrightarrow> color_of (rbt_recolor t) = color.B"
  by (induction t rule: rbt_recolor.induct) (auto simp: is_rbt_aux_def)

lemma is_rbt_recolor: "is_rbt_aux t \<Longrightarrow> is_rbt (rbt_recolor t)"
  using color_of_rbt_recolor rbt_recolor rbt_sorted_recolor
  by (auto simp: is_rbt_prop is_rbt_aux_prop)

lemma is_rbt_dest: "is_rbt t \<Longrightarrow> is_rbt_aux t"
  by (auto simp: is_rbt_prop)

lemma is_rbt_union: "is_rbt t1 \<Longrightarrow> is_rbt t2 \<Longrightarrow> is_rbt (rbt_recolor (union t1 t2))"
  using is_rbt_aux_union
  by (auto dest!: is_rbt_dest intro: is_rbt_recolor)

lemma is_rbt_inter: "is_rbt t1 \<Longrightarrow> is_rbt t2 \<Longrightarrow> is_rbt (rbt_recolor (inter t1 t2))"
  using is_rbt_aux_inter
  by (auto dest!: is_rbt_dest intro: is_rbt_recolor)

lemma is_rbt_minus: "is_rbt t1 \<Longrightarrow> is_rbt t2 \<Longrightarrow> is_rbt (rbt_recolor (minus t1 t2))"
  using is_rbt_aux_minus
  by (auto dest!: is_rbt_dest intro: is_rbt_recolor)

end

lemma is_rbt_union_comp:
  assumes "ID ccompare = Some (c :: ('a :: ccompare) comparator)"
    "ord.is_rbt (lt_of_comp c) t1" "ord.is_rbt (lt_of_comp c) t2"
  shows "ord.is_rbt (lt_of_comp c) (rbt_recolor (union_comp c t1 t2))"
  using linorder.is_rbt_union[OF ID_ccompare[OF assms(1)] assms(2,3)]
    union_comp[OF ID_ccompare'[OF assms(1)]]
  by auto

lift_definition rbt_union_rbt_join2 :: "'a :: ccompare set_rbt \<Rightarrow> 'a set_rbt \<Rightarrow> 'a set_rbt" is
  "\<lambda>t1 t2. rbt_recolor (union_comp ccomp t1 t2)"
  using is_rbt_union_comp
  by force

lemma is_rbt_inter_comp:
  assumes "ID ccompare = Some (c :: ('a :: ccompare) comparator)"
    "ord.is_rbt (lt_of_comp c) t1" "ord.is_rbt (lt_of_comp c) t2"
  shows "ord.is_rbt (lt_of_comp c) (rbt_recolor (inter_comp c t1 t2))"
  using linorder.is_rbt_inter[OF ID_ccompare[OF assms(1)] assms(2,3)]
    inter_comp[OF ID_ccompare'[OF assms(1)]]
  by auto

lift_definition rbt_inter_rbt_join2 :: "'a :: ccompare set_rbt \<Rightarrow> 'a set_rbt \<Rightarrow> 'a set_rbt" is
  "\<lambda>t1 t2. rbt_recolor (inter_comp ccomp t1 t2)"
  using is_rbt_inter_comp
  by force

lemma is_rbt_minus_comp:
  assumes "ID ccompare = Some (c :: ('a :: ccompare) comparator)"
    "ord.is_rbt (lt_of_comp c) t1" "ord.is_rbt (lt_of_comp c) t2"
  shows "ord.is_rbt (lt_of_comp c) (rbt_recolor (minus_comp c t1 t2))"
  using linorder.is_rbt_minus[OF ID_ccompare[OF assms(1)] assms(2,3)]
    minus_comp[OF ID_ccompare'[OF assms(1)]]
  by auto

lift_definition rbt_minus_rbt_join2 :: "'a :: ccompare set_rbt \<Rightarrow> 'a set_rbt \<Rightarrow> 'a set_rbt" is
  "\<lambda>t1 t2. rbt_recolor (minus_comp ccomp t1 t2)"
  using is_rbt_minus_comp
  by force

lemma rbt_recolor_keys[simp]: "set (RBT_Impl.keys (rbt_recolor t)) = set (RBT_Impl.keys t)"
  by (induction t rule: rbt_recolor.induct) auto

lemma rbt_union_rbt_join2_set:
  fixes t1 :: "('a :: ccompare, unit) mapping_rbt"
  assumes "ID (ccompare :: 'a comparator option) \<noteq> None"
  shows "RBT_set t1 \<union> RBT_set t2 = RBT_set (rbt_union_rbt_join2 t1 t2)"
  unfolding RBT_set_conv_keys[OF assms]
  using assms
proof (transfer)
  fix t1 :: "('a, unit) rbt"
  fix t2 :: "('a, unit) rbt"
  have id_ccomp: "ID ccompare = Some (ccomp :: 'a comparator)"
    using assms
    by auto
  then have c: "comparator (ccomp :: 'a comparator)"
    by (auto simp: ID_ccompare')
  assume "ord.is_rbt cless t1 \<or> ID ccompare = (None :: 'a comparator option)"
    "ord.is_rbt cless t2 \<or> ID ccompare = (None :: 'a comparator option)"
  then have rbt_sorted_t: "ord.rbt_sorted cless t1" "ord.rbt_sorted cless t2"
    using assms
    by (auto simp: ord.is_rbt_def)
  show "set (RBT_Impl.keys t1) \<union> set (RBT_Impl.keys t2) =
    set (RBT_Impl.keys (rbt_recolor (union_comp ccomp t1 t2)))"
    using linorder.rbt_sorted_union[OF ID_ccompare[OF id_ccomp] rbt_sorted_t]
    by (auto simp: union_comp[OF c])
qed

lemma rbt_union_code:
  fixes t1 t2 :: "'a :: ccompare set_rbt"
  shows "RBT_set t1 \<union> RBT_set t2 =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''union RBT_set RBT_set: ccompare = None'')
      (\<lambda>_. RBT_set t1 \<union> RBT_set t2)
    | Some _ \<Rightarrow> RBT_set (rbt_union_rbt_join2 t1 t2))"
  using rbt_union_rbt_join2_set
  by (auto split: option.splits)

lemma rbt_inter_rbt_join2_set:
  fixes t1 :: "('a :: ccompare, unit) mapping_rbt"
  assumes "ID (ccompare :: 'a comparator option) \<noteq> None"
  shows "RBT_set t1 \<inter> RBT_set t2 = RBT_set (rbt_inter_rbt_join2 t1 t2)"
  unfolding RBT_set_conv_keys[OF assms]
  using assms
proof (transfer)
  fix t1 :: "('a, unit) rbt"
  fix t2 :: "('a, unit) rbt"
  have id_ccomp: "ID ccompare = Some (ccomp :: 'a comparator)"
    using assms
    by auto
  then have c: "comparator (ccomp :: 'a comparator)"
    by (auto simp: ID_ccompare')
  assume "ord.is_rbt cless t1 \<or> ID ccompare = (None :: 'a comparator option)"
  then have rbt_sorted_t1: "ord.rbt_sorted cless t1"
    using assms
    by (auto simp: ord.is_rbt_def)
  assume "ord.is_rbt cless t2 \<or> ID ccompare = (None :: 'a comparator option)"
  then have rbt_sorted_t2: "ord.rbt_sorted cless t2"
    using assms
    by (auto simp: ord.is_rbt_def)
  show "set (RBT_Impl.keys t1) \<inter> set (RBT_Impl.keys t2) =
    set (RBT_Impl.keys (rbt_recolor (inter_comp ccomp t1 t2)))"
    using linorder.rbt_sorted_inter[OF ID_ccompare[OF id_ccomp] rbt_sorted_t1 rbt_sorted_t2]
    by (auto simp: inter_comp[OF c])
qed

lemma rbt_inter_code:
  fixes t1 t2 :: "'a :: ccompare set_rbt"
  shows "RBT_set t1 \<inter> RBT_set t2 =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''inter RBT_set RBT_set: ccompare = None'')
      (\<lambda>_. RBT_set t1 \<inter> RBT_set t2)
    | Some _ \<Rightarrow> RBT_set (rbt_inter_rbt_join2 t1 t2))"
  using rbt_inter_rbt_join2_set
  by (auto split: option.splits)

lemma rbt_minus_rbt_join2_set:
  fixes t1 :: "('a :: ccompare, unit) mapping_rbt"
  assumes "ID (ccompare :: 'a comparator option) \<noteq> None"
  shows "RBT_set t1 - RBT_set t2 = RBT_set (rbt_minus_rbt_join2 t1 t2)"
  unfolding RBT_set_conv_keys[OF assms]
  using assms
proof (transfer)
  fix t1 :: "('a, unit) rbt"
  fix t2 :: "('a, unit) rbt"
  have id_ccomp: "ID ccompare = Some (ccomp :: 'a comparator)"
    using assms
    by auto
  then have c: "comparator (ccomp :: 'a comparator)"
    by (auto simp: ID_ccompare')
  assume "ord.is_rbt cless t1 \<or> ID ccompare = (None :: 'a comparator option)"
  then have rbt_sorted_t1: "rbt t1" "ord.rbt_sorted cless t1"
    using assms
    by (auto simp: ord.is_rbt_def rbt_def)
  assume "ord.is_rbt cless t2 \<or> ID ccompare = (None :: 'a comparator option)"
  then have rbt_sorted_t2: "ord.rbt_sorted cless t2"
    using assms
    by (auto simp: ord.is_rbt_def)
  show "set (RBT_Impl.keys t1) - set (RBT_Impl.keys t2) =
    set (RBT_Impl.keys (rbt_recolor (minus_comp ccomp t1 t2)))"
    using linorder.rbt_sorted_minus[OF ID_ccompare[OF id_ccomp] rbt_sorted_t1 rbt_sorted_t2]
    by (auto simp: minus_comp[OF c])
qed

lemma rbt_minus_code:
  fixes t1 t2 :: "'a :: ccompare set_rbt"
  shows "RBT_set t1 - RBT_set t2 =
    (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''minus RBT_set RBT_set: ccompare = None'')
      (\<lambda>_. RBT_set t1 - RBT_set t2)
    | Some _ \<Rightarrow> RBT_set (rbt_minus_rbt_join2 t1 t2))"
  using rbt_minus_rbt_join2_set
  by (auto split: option.splits)

typedef (overloaded) 'a sdlist = "{xs :: ('a :: ccompare) list.
  case ID CCOMPARE('a) of None \<Rightarrow> xs = [] | Some _ \<Rightarrow> linorder.sorted cless_eq xs \<and> distinct xs}"
  by (auto intro!: exI[of _ "[]"] split: option.splits)
     (metis keys_eq_Nil_iff sorted_RBT_Set_keys)

setup_lifting type_definition_sdlist

lift_definition sdlist_of_list :: "('a :: ccompare) list \<Rightarrow> 'a sdlist" is
  "\<lambda>xs. case ID CCOMPARE('a) of None \<Rightarrow> [] | Some _ \<Rightarrow> remdups (linorder.sort cless_eq xs)"
  using linorder.sorted_sort[OF ID_ccompare] linorder.sorted_remdups[OF ID_ccompare]
  by (auto split: option.splits)

lemma set_sdlist_of_list:
  fixes xs :: "('a :: ccompare) list"
    and c :: "'a comparator"
  assumes assms: "ID ccompare = Some c"
  shows "set (Rep_sdlist (sdlist_of_list xs)) = set xs"
  using assms
  by transfer (fastforce simp: linorder.set_sort[OF ID_ccompare])

lemma sset_rbt:
  fixes xs :: "('a :: ccompare) list"
    and c :: "'a comparator"
  assumes assms: "ID ccompare = Some c" "linorder.sorted cless_eq xs" "distinct xs"
  shows "ord.is_rbt cless (rbtreeify (map (\<lambda>x. (x, ())) xs))"
  using assms linorder.is_rbt_rbtreeify[OF ID_ccompare[OF assms(1)], of "map (\<lambda>x. (x, ())) xs"]
  by (auto simp: comp_def)

lift_definition sset :: "('a :: ccompare) sdlist \<Rightarrow> 'a set_rbt" is
  "\<lambda>xs. rbtreeify (map (\<lambda>x. (x, ())) xs)"
  using sset_rbt
  by fastforce

lemma Rep_sdlist_keys:
  fixes xs :: "('a :: ccompare) sdlist"
  shows "Rep_sdlist xs = RBT_Set2.keys (sset xs)"
  by transfer (auto simp: RBT_Impl.keys_def comp_def)

lemma rbt_comp_lookup_iff_in_set:
  fixes x :: "'a :: ccompare"
    and xs :: "'a list"
    and c :: "'a comparator"
  assumes "ID ccompare = Some c" "linorder.sorted cless_eq xs" "distinct xs"
  shows "rbt_comp_lookup ccomp (rbtreeify (map (\<lambda>x. (x, ())) xs)) x = Some () \<longleftrightarrow> x \<in> set xs"
  using linorder.rbt_lookup_rbtreeify[OF ID_ccompare[OF assms(1)], of "map (\<lambda>x. (x, ())) xs"]
      assms(2,3)
  by (auto simp: rbt_comp_lookup[OF ID_ccompare'[OF assms(1)]] assms(1) map_of_map_Pair_const
      comp_def)

lemma RBT_set_sset:
  fixes xs :: "('a :: ccompare) sdlist"
  shows "RBT_set (sset xs) = set (Rep_sdlist xs)"
  unfolding RBT_set_def
  apply transfer
  using rbt_comp_lookup_iff_in_set
  by (fastforce simp: rbtreeify_def split: option.splits)

lemma set_code:
  fixes xs :: "('a :: ccompare) list"
  shows "set xs = (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''set: ccompare = None'')
    (\<lambda>_. set xs)
  | Some _ \<Rightarrow> RBT_set (sset (sdlist_of_list xs)))"
  by (auto simp: RBT_set_sset set_sdlist_of_list split: option.splits)

lemma linorder_sorted_upt: "linorder.sorted (le_of_comp compare) [n..<n']"
proof -
  define c :: "nat comparator" where "c = compare"
  have cl: "class.linorder (le_of_comp c) (lt_of_comp c)"
    by (auto simp: c_def ID_ccompare ID_Some ccompare_nat_def)
  show ?thesis
    using linorder.sorted_sorted_wrt[OF cl] sorted_wrt_mono_rel[OF _ sorted_wrt_upt]
    by (auto simp: c_def ord_defs(1))
qed

lift_definition upt_sdlist :: "nat \<Rightarrow> nat \<Rightarrow> nat sdlist" is upt
  using linorder_sorted_upt
  by (auto simp: ID_Some ccompare_nat_def split: option.splits)

definition nat_set_upt :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "nat_set_upt i j = {i..<j}"

lemma nat_set_upt_prop: "nat_set_upt i j = RBT_set (sset (upt_sdlist i j))"
  by (auto simp: nat_set_upt_def RBT_set_sset upt_sdlist.rep_eq)

declare Set_union_code(1)[code del]
declare rbt_union_code[code]
declare Set_inter_code(16)[code del]
declare rbt_inter_code[code]

(* Set_minus on RBTs not supported in Set_Impl! *)
declare Set_minus_code[code del]
declare rbt_minus_code[code]

(*
The following code equation requires an executable sorting algorithm for ccompare.
declare Set_Impl.set_code[code del]
declare set_code[code]
*)

declare nat_set_upt_prop[code]

end