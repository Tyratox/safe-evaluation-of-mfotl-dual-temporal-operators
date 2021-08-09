(*<*)
theory Formula
  imports
    Event_Data
    Regex
    "MFOTL_Monitor_Devel.Interval"
    "MFOTL_Monitor_Devel.Trace"
    "MFOTL_Monitor_Devel.Abstract_Monitor"
    "HOL-Library.Mapping"
    Containers.Set_Impl
begin
(*>*)

section \<open>Metric first-order dynamic logic\<close>

derive (eq) ceq enat

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

context begin

subsection \<open>Formulas and satisfiability\<close>

qualified type_synonym name = string8
qualified type_synonym event = "(name \<times> event_data list)"
qualified type_synonym database = "(name, event_data list set list) mapping"
qualified type_synonym prefix = "(name \<times> event_data list) prefix"
qualified type_synonym trace = "(name \<times> event_data list) trace"

qualified type_synonym env = "event_data list"

subsubsection \<open>Syntax\<close>

qualified datatype trm = is_Var: Var nat | is_Const: Const event_data
  | Plus trm trm | Minus trm trm | UMinus trm | Mult trm trm | Div trm trm | Mod trm trm
  | F2i trm | I2f trm

qualified primrec fvi_trm :: "nat \<Rightarrow> trm \<Rightarrow> nat set" where
  "fvi_trm b (Var x) = (if b \<le> x then {x - b} else {})"
| "fvi_trm b (Const _) = {}"
| "fvi_trm b (Plus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Minus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (UMinus x) = fvi_trm b x"
| "fvi_trm b (Mult x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Div x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Mod x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (F2i x) = fvi_trm b x"
| "fvi_trm b (I2f x) = fvi_trm b x"

abbreviation "fv_trm \<equiv> fvi_trm 0"

qualified primrec eval_trm :: "env \<Rightarrow> trm \<Rightarrow> event_data" where
  "eval_trm v (Var x) = v ! x"
| "eval_trm v (Const x) = x"
| "eval_trm v (Plus x y) = eval_trm v x + eval_trm v y"
| "eval_trm v (Minus x y) = eval_trm v x - eval_trm v y"
| "eval_trm v (UMinus x) = - eval_trm v x"
| "eval_trm v (Mult x y) = eval_trm v x * eval_trm v y"
| "eval_trm v (Div x y) = eval_trm v x div eval_trm v y"
| "eval_trm v (Mod x y) = eval_trm v x mod eval_trm v y"
| "eval_trm v (F2i x) = EInt (integer_of_event_data (eval_trm v x))"
| "eval_trm v (I2f x) = EFloat (double_of_event_data (eval_trm v x))"

lemma eval_trm_fv_cong: "\<forall>x\<in>fv_trm t. v ! x = v' ! x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (induction t) simp_all


qualified datatype agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
qualified type_synonym agg_op = "agg_type \<times> event_data"

definition flatten_multiset :: "(event_data \<times> enat) set \<Rightarrow> event_data list" where
  "flatten_multiset M = concat (map (\<lambda>(x, c). replicate (the_enat c) x) (csorted_list_of_set M))"

fun eval_agg_op :: "agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op (Agg_Cnt, y0) M = EInt (integer_of_int (length (flatten_multiset M)))"
| "eval_agg_op (Agg_Min, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl min x xs)"
| "eval_agg_op (Agg_Max, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl max x xs)"
| "eval_agg_op (Agg_Sum, y0) M = foldl plus y0 (flatten_multiset M)"
| "eval_agg_op (Agg_Avg, y0) M = EFloat (let xs = flatten_multiset M in case xs of
      [] \<Rightarrow> 0
    | _ \<Rightarrow> double_of_event_data (foldl plus (EInt 0) xs) / double_of_int (length xs))"
| "eval_agg_op (Agg_Med, y0) M = EFloat (let xs = flatten_multiset M; u = length xs in
    if u = 0 then 0 else
      let u' = u div 2 in
      if even u then
        (double_of_event_data (xs ! (u'-1)) + double_of_event_data (xs ! u') / double_of_int 2)
      else double_of_event_data (xs ! u'))"

qualified datatype (discs_sels) formula = Pred name "trm list"
  | Let name formula formula
  | Eq trm trm | Less trm trm | LessEq trm trm
  | Neg formula | Or formula formula | And formula formula | Ands "formula list" | Exists formula
  | Agg nat agg_op nat trm formula
  | Prev \<I> formula | Next \<I> formula
  | Since formula \<I> formula | Until formula \<I> formula
  | Trigger formula \<I> formula | Release formula \<I> formula
  | MatchF \<I> "formula Regex.regex" | MatchP \<I> "formula Regex.regex"

qualified definition "FF = Exists (Neg (Eq (Var 0) (Var 0)))"
qualified definition "TT \<equiv> Neg FF"

qualified fun fvi :: "nat \<Rightarrow> formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Let p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Less t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (LessEq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Ands \<phi>s) = (let xs = map (fvi b) \<phi>s in \<Union>x\<in>set xs. x)"
| "fvi b (Exists \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Agg y \<omega> b' f \<phi>) = fvi (b + b') \<phi> \<union> fvi_trm (b + b') f \<union> (if b \<le> y then {y - b} else {})"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Trigger \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Release \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
| "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"

abbreviation "fv \<equiv> fvi 0"
abbreviation "fv_regex \<equiv> Regex.fv_regex fv"

lemma fv_abbrevs[simp]: "fv TT = {}" "fv FF = {}"
  unfolding TT_def FF_def by auto

lemma fvi_abbrevs[simp]: "\<forall>b. fvi b TT = {}" "\<forall>b. fvi b FF = {}"
  unfolding TT_def FF_def by auto

lemma fv_subset_Ands: "\<phi> \<in> set \<phi>s \<Longrightarrow> fv \<phi> \<subseteq> fv (Ands \<phi>s)"
  by auto

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (induction t) simp_all

lemma finite_fvi[simp]: "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all

lemma fvi_plus: "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> b' f \<phi>)
  have *: "b + c + b' = b + b' + c" by simp
  from Agg show ?case by (force simp: * fvi_trm_plus)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

lemma fvi_Suc: "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  using fvi_plus[where c=1] by simp

lemma fvi_plus_bound:
  assumes "\<forall>i\<in>fvi (b + c) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < c + n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  show "i < c + n"
  proof (cases "i < c")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain i' where "i = i' + c"
      using nat_le_iff_add by (auto simp: not_less)
    with assms \<open>i \<in> fvi b \<phi>\<close> show ?thesis by (simp add: fvi_plus)
  qed
qed

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
  using assms fvi_plus_bound[where c=1] by simp

lemma fvi_iff_fv: "x \<in> fvi b \<phi> \<longleftrightarrow> x + b \<in> fv \<phi>"
  using fvi_plus[where b=0 and c=b] by simp_all

qualified definition nfv :: "formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified abbreviation nfv_regex where
  "nfv_regex \<equiv> Regex.nfv_regex fv"

qualified definition envs :: "formula \<Rightarrow> env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Let p \<phi> \<psi>) = nfv \<psi>"
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (MatchP I r) = Regex.nfv_regex fv r"
  "nfv (MatchF I r) = Regex.nfv_regex fv r"
  "nfv_regex (Regex.Skip n) = 0"
  "nfv_regex (Regex.Test \<phi>) = Max (insert 0 (Suc ` fv \<phi>))"
  "nfv_regex (Regex.Plus r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Times r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Star r) = nfv_regex r"
  unfolding nfv_def Regex.nfv_regex_def by (simp_all add: image_Un Max_Un[symmetric])

lemma nfv_Ands[simp]: "nfv (Ands l) = Max (insert 0 (nfv ` set l))"
proof (induction l)
  case Nil
  then show ?case unfolding nfv_def by simp
next
  case (Cons a l)
  have "fv (Ands (a # l)) = fv a \<union> fv (Ands l)" by simp
  then have "nfv (Ands (a # l)) = max (nfv a) (nfv (Ands l))"
    unfolding nfv_def
    by (auto simp: image_Un Max.union[symmetric])
  with Cons.IH show ?case
    by (cases l) auto
qed

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

lemma fvi_less_nfv_regex: "\<forall>i\<in>fv_regex \<phi>. i < nfv_regex \<phi>"
  unfolding Regex.nfv_regex_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

subsubsection \<open>Future reach\<close>

qualified fun future_bounded :: "formula \<Rightarrow> bool" where
  "future_bounded (Pred _ _) = True"
| "future_bounded (Let p \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Eq _ _) = True"
| "future_bounded (Less _ _) = True"
| "future_bounded (LessEq _ _) = True"
| "future_bounded (Neg \<phi>) = future_bounded \<phi>"
| "future_bounded (Or \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (And \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Ands l) = list_all future_bounded l"
| "future_bounded (Exists \<phi>) = future_bounded \<phi>"
| "future_bounded (Agg y \<omega> b f \<phi>) = future_bounded \<phi>"
| "future_bounded (Prev I \<phi>) = future_bounded \<phi>"
| "future_bounded (Next I \<phi>) = future_bounded \<phi>"
| "future_bounded (Since \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Until \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> bounded I)"
| "future_bounded (Trigger \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Release \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> bounded I)"
| "future_bounded (MatchP I r) = Regex.pred_regex future_bounded r"
| "future_bounded (MatchF I r) = (Regex.pred_regex future_bounded r \<and> bounded I)"

subsubsection \<open>Semantics\<close>

definition "ecard A = (if finite A then card A else \<infinity>)"

qualified fun sat :: "trace \<Rightarrow> (name \<rightharpoonup> nat \<Rightarrow> event_data list set) \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> formula \<Rightarrow> bool" where
  "sat \<sigma> V v i (Pred r ts) = (case V r of
       None \<Rightarrow> (r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> map (eval_trm v) ts \<in> X i)"
| "sat \<sigma> V v i (Let p \<phi> \<psi>) =
    sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = nfv \<phi> \<and> sat \<sigma> V v i \<phi>})) v i \<psi>"
| "sat \<sigma> V v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> V v i (Less t1 t2) = (eval_trm v t1 < eval_trm v t2)"
| "sat \<sigma> V v i (LessEq t1 t2) = (eval_trm v t1 \<le> eval_trm v t2)"
| "sat \<sigma> V v i (Neg \<phi>) = (\<not> sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Or \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<or> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (And \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (Ands l) = (\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Exists \<phi>) = (\<exists>z. sat \<sigma> V (z # v) i \<phi>)"
| "sat \<sigma> V v i (Agg y \<omega> b f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = b \<and> sat \<sigma> V (zs @ v) i \<phi> \<and> eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M)"
| "sat \<sigma> V v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
| "sat \<sigma> V v i (Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat \<sigma> V v (Suc i) \<phi>)"
| "sat \<sigma> V v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = (\<forall>j\<le>i. (mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)))"
| "sat \<sigma> V v i (Release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
| "sat \<sigma> V v i (MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat \<sigma> V v) r j i)"
| "sat \<sigma> V v i (MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat \<sigma> V v) r i j)"

lemma sat_abbrevs[simp]:
  "sat \<sigma> V v i TT" "\<not> sat \<sigma> V v i FF"
  unfolding TT_def FF_def by auto

lemma sat_Ands: "sat \<sigma> V v i (Ands l) \<longleftrightarrow> (\<forall>\<phi>\<in>set l. sat \<sigma> V v i \<phi>)"
  by (simp add: list_all_iff)

lemma sat_Until_rec: "sat \<sigma> V v i (Until \<phi> I \<psi>) \<longleftrightarrow>
  memL I 0 \<and> sat \<sigma> V v i \<psi> \<or>
  (memR I (\<Delta> \<sigma> (i + 1)) \<and> sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "i \<le> j" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1,2) have "memR I (\<Delta> \<sigma> (i + 1))"
      by (auto elim: order_trans[rotated] simp: diff_le_mono)
    moreover from False j(1,4) have "sat \<sigma> V v i \<phi>" by auto
    moreover from False j have "sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
      by (auto intro!: exI[of _ j])
    ultimately show ?thesis by blast
  qed simp
next
  assume \<Delta>: "memR I (\<Delta> \<sigma> (i + 1))" and now: "sat \<sigma> V v i \<phi>" and
   "next": "sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
  from "next" obtain j where j: "i + 1 \<le> j" "mem ((subtract (\<Delta> \<sigma> (i + 1)) I)) (\<tau> \<sigma> j - \<tau> \<sigma> (i + 1))"
      "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {i + 1 ..< j}. sat \<sigma> V v k \<phi>"
    by (auto simp: diff_le_mono memL_mono)
  from \<Delta> j(1,2) have "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    by auto
  with now j(1,3,4) show ?L by (auto simp: le_eq_less_or_eq[of i] intro!: exI[of _ j])
qed auto

lemma sat_Since_rec: "sat \<sigma> V v i (Since \<phi> I \<psi>) \<longleftrightarrow>
  mem I 0 \<and> sat \<sigma> V v i \<psi> \<or>
  (i > 0 \<and> memR I (\<Delta> \<sigma> i) \<and> sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1) obtain k where [simp]: "i = k + 1"
      by (cases i) auto
    with j(1,2) False have "memR I (\<Delta> \<sigma> i)"
      by (auto elim: order_trans[rotated] simp: diff_le_mono2 le_Suc_eq)
    moreover from False j(1,4) have "sat \<sigma> V v i \<phi>" by auto
    moreover from False j have "sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
      by (auto intro!: exI[of _ j])
    ultimately show ?thesis by auto
  qed simp
next
  assume i: "0 < i" and \<Delta>: "memR I (\<Delta> \<sigma> i)" and now: "sat \<sigma> V v i \<phi>" and
   "prev": "sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
  from "prev" obtain j where j: "j \<le> i - 1" "mem (subtract (\<Delta> \<sigma> i) I) (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j)"
      "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {j <.. i - 1}. sat \<sigma> V v k \<phi>"
    by (auto simp: diff_le_mono2 memL_mono)
  from \<Delta> i j(1,2) have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    by auto
  with now i j(1,3,4) show ?L by (auto simp: le_Suc_eq gr0_conv_Suc intro!: exI[of _ j])
qed auto

lemma sat_MatchF_rec: "sat \<sigma> V v i (MatchF I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  memR I (\<Delta> \<sigma> (i + 1)) \<and> (\<exists>s \<in> Regex.lpd (sat \<sigma> V v) i r. sat \<sigma> V v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" and "Regex.match (sat \<sigma> V v) r i j" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "i < j")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r i j\<close> lpd_match[of i j "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.lpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s (i + 1) j" by auto
    with True j have ?R2
      by (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans[rotated])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "memR I (\<Delta> \<sigma> (i + 1))"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.lpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s)"
  then obtain j where "j > i" "Regex.match (sat \<sigma> V v) s (i + 1) j"
    "mem (subtract (\<Delta> \<sigma> (i + 1)) I) (\<tau> \<sigma> j - \<tau> \<sigma> (Suc i))"
    by (auto simp: diff_le_mono memL_mono Suc_le_eq)
  ultimately show ?L
    by (auto simp: le_diff_conv lpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_MatchP_rec: "sat \<sigma> V v i (MatchP I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  i > 0 \<and> memR I (\<Delta> \<sigma> i) \<and> (\<exists>s \<in> Regex.rpd (sat \<sigma> V v) i r. sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" and "Regex.match (sat \<sigma> V v) r j i" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "j < i")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r j i\<close> rpd_match[of j i "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.rpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s j (i - 1)" by auto
    with True j have ?R2
      by (auto simp: diff_le_mono2 intro!: exI[of _ j])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "memR I (\<Delta> \<sigma> i)"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.rpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s)" "i > 0"
  then obtain j where "j < i" "Regex.match (sat \<sigma> V v) s j (i - 1)"
    "mem (subtract (\<Delta> \<sigma> i) I) (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j)" by (auto simp: gr0_conv_Suc less_Suc_eq_le)
  ultimately show ?L
    by (auto simp: rpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_Since_0: "sat \<sigma> V v 0 (Since \<phi> I \<psi>) \<longleftrightarrow> memL I 0 \<and> sat \<sigma> V v 0 \<psi>"
  by auto

lemma sat_MatchP_0: "sat \<sigma> V v 0 (MatchP I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) 0 r"
  by (auto simp: eps_match)

lemma sat_Since_point: "sat \<sigma> V v i (Since \<phi> I \<psi>) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow> sat \<sigma> V v i (Since \<phi> (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<psi>) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_MatchP_point: "sat \<sigma> V v i (MatchP I r) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow> sat \<sigma> V v i (MatchP (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) r) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_Since_pointD: "sat \<sigma> V v i (Since \<phi> (point t) \<psi>) \<Longrightarrow> mem I t \<Longrightarrow> sat \<sigma> V v i (Since \<phi> I \<psi>)"
  by auto

lemma sat_MatchP_pointD: "sat \<sigma> V v i (MatchP (point t) r) \<Longrightarrow> mem I t \<Longrightarrow> sat \<sigma> V v i (MatchP I r)"
  by auto

lemma sat_fv_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
proof (induct \<phi> arbitrary: V v v' i rule: formula.induct)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]] split: option.splits)
next
  case (Let p b \<phi> \<psi>)
  then show ?case
    by auto
next
  case (Eq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Less x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (LessEq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case using sat_Ands by blast
next
  case (Exists \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "v ! y = v' ! y"
    using Agg.prems by simp
  moreover have "sat \<sigma> V (zs @ v) i \<phi> = sat \<sigma> V (zs @ v') i \<phi>" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  moreover have "eval_trm (zs @ v) f = eval_trm (zs @ v') f" if "length zs = b" for zs
    using that Agg.prems by (auto intro!: eval_trm_fv_cong[where v="zs @ v" and v'="zs @ v'"]
        simp: nth_append fvi_iff_fv(1)[where b=b] fvi_trm_iff_fv_trm[where b="length zs"])
  ultimately show ?case
    by (simp cong: conj_cong)
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (Trigger \<phi> I \<psi>)
  show ?case
    using Trigger(1, 2)[of v v'] Trigger(3)
    by auto
next
  case (Release \<phi> I \<psi>)
  show ?case
    using Release(1, 2)[of v v'] Release(3)
    by auto
qed (auto 10 0 split: nat.splits intro!: iff_exI)

lemma match_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
  by (rule match_fv_cong, rule sat_fv_cong) (auto simp: fv_regex_alt)

lemma eps_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.eps (sat \<sigma> V v) i r = Regex.eps (sat \<sigma> V v') i r"
  unfolding eps_match by (erule match_fv_cong[THEN fun_cong, THEN fun_cong])

subsubsection \<open>Trigger / Release\<close>

lemma interval_geq:
  fixes i j :: nat
  assumes "memL I a"
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
  assumes "j \<le> k"
  assumes "a \<le> (\<tau> \<sigma> i - \<tau> \<sigma> k)"
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  from assms(3) assms(4) have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" by auto
  then have "(\<tau> \<sigma> i - \<tau> \<sigma> j) \<ge> (\<tau> \<sigma> i - \<tau> \<sigma> k)" by linarith
  then have "memR I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    using assms(1) assms(2) assms(4)
    by auto
  thus ?thesis by auto
qed

lemma interval_leq:
  fixes i j :: nat
  assumes "memL I a"
  assumes "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  assumes "k \<le> j"
  assumes "a \<le> (\<tau> \<sigma> k - \<tau> \<sigma> i)"
  shows "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
proof -
  from assms(3) assms(4) have "\<tau> \<sigma> j \<ge> \<tau> \<sigma> k" by auto
  then have "(\<tau> \<sigma> j - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> k - \<tau> \<sigma> i)" by linarith
  with assms(1) assms(2) assms(4) have "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> memL I (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
  thus ?thesis by auto
qed

lemma interval_all: "mem all i"
  by transfer auto

qualified definition "first = Neg (Prev all TT)"

lemma first_sat[simp] : "sat \<sigma> V v i first = (i=0)"
  using interval_all by (auto simp: first_def split: nat.split)

lemma first_fvi[simp]: "fvi b first = {}"
  by (auto simp: first_def TT_def FF_def split: nat.split)

lemma interval_bounds:
  fixes a:: nat
  fixes b:: enat
  fixes I::\<I>
  assumes "a \<le> b"
  assumes "I = interval a b"
  shows "memL I = (\<lambda>i. a \<le> i) \<and> memR I = (\<lambda>i. enat i \<le> b) \<and> (bounded I = (b \<noteq> \<infinity>))"
  using assms
  by transfer auto

(* [a, b] \<Rightarrow> [b+1, \<infinity>] *)
lift_definition flip_int :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if bounded I then ((\<lambda>i. \<not>memR I i), (\<lambda>i. True), False) else ((\<lambda>i. True), (\<lambda>i. True), False)"
  by transfer (auto simp: upclosed_def downclosed_def)

(* [a, b] \<Rightarrow> [b+1, 2b]. nonempty if b+1\<le>2b \<Leftrightarrow> 1\<le>b *)
lift_definition flip_int_double_upper :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if (bounded I) then ((\<lambda>i. \<not>memR I i), (\<lambda>i. memR I ((div) i 2)), True) else ((\<lambda>i. True), (\<lambda>i. True), False)"
proof -
  define A where "A = {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
  {
    fix I :: \<I>
    assume I_props: "bounded I"
    define B where "B = {x. \<not> memR I x}"
    define b where "b = Inf B"
    define x where "x = 2 * b"
    have up: "upclosed (\<lambda>i. \<not> memR I i)"
      using memR_antimono upclosed_def
      by blast
    {
      fix r m
      assume assumptions: "(\<lambda>i. memR I ((div) i 2)) r" "m\<le>r"
      then have "(\<lambda>i. memR I ((div) i 2)) m" by auto
    }
    then have "\<forall>m r. (\<lambda>i. memR I ((div) i 2)) r \<longrightarrow> m \<le> r \<longrightarrow> (\<lambda>i. memR I ((div) i 2)) m" by auto
    then have down: "downclosed (\<lambda>i. memR I ((div) i 2))" using downclosed_def by auto
    have "\<exists>b. \<not>memR I b" using I_props bounded_memR by auto
    then have B_props: "B \<noteq> {}" using B_def by auto
    then have "b \<in> B" using b_def by (simp add: Inf_nat_def1)
    then have b_props: "\<not> memR I b" using B_def by auto
    then have "0 < b" using memR_nonzeroD by blast
    then have b_half_props: "(b div 2) < b" by auto
    {
      assume "\<not> memR I (b div 2)"
      then have "(b div 2) \<in> B" using B_def by blast
      then have "(b div 2) \<ge> b" using cInf_lower b_def by auto
      then have "False" using b_half_props by auto
    }
    then have "memR I (b div 2)" by blast
    moreover have "\<not>memR I (x div 2)" using x_def b_props by auto
    ultimately have "(\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) \<in> A"
      using b_props A_def up down
      by auto
  }
  then have "\<forall>I. bounded I \<longrightarrow> (\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) \<in> A" by auto
  moreover have "\<forall>I. \<not>bounded I \<longrightarrow> (\<lambda>i. True, \<lambda>i. True, False) \<in> A"
    using A_def
    by (metis Interval.all.rep_eq Rep_\<I>)
  ultimately have "\<forall>I. (if bounded I then (\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) else (\<lambda>i. True, \<lambda>i. True, False)) \<in> A"
    by (auto split: if_splits)
  then show "\<And>\<I>. (if bounded \<I> then (\<lambda>i. \<not> memR \<I> i, \<lambda>i. memR \<I> (i div 2), True) else (\<lambda>i. True, \<lambda>i. True, False))
         \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using A_def
    by auto
qed

(* [a, b] \<Rightarrow> [0, a-1] *)
lift_definition flip_int_less_lower :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if \<not>memL I 0 then ((\<lambda>i. True), (\<lambda>i. \<not>memL I i), True) else ((\<lambda>i. True), (\<lambda>i. True), False)"
  by transfer (auto simp: upclosed_def downclosed_def)

(* [a, b] \<Rightarrow> [0, b] *)
lift_definition int_remove_lower_bound :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. ((\<lambda>i. True), (\<lambda>i. memR I i), bounded I)"
  by transfer (auto simp: upclosed_def downclosed_def)

lemma flip_int_props:
  assumes "bounded I"
  assumes "I' = flip_int I"
  shows "\<not>bounded I' \<and> \<not>mem I' 0"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_props:
  assumes "\<not>memL I 0" (* [a, b] *)
  assumes "I' = flip_int_less_lower I" (* [0, a-1] *)
  shows "mem I' 0 \<and> bounded I'"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_memL:
  assumes "\<not>memL I x" (* [a, b], x < a *)
  shows "memL (flip_int_less_lower I) x" (* x \<in> [0, a-1] *)
  using assms
  by (transfer') (simp)

lemma flip_int_less_lower_memR:
  assumes "\<not>memL I 0" (* I = [a, b], I' = [0, a-1]. x \<le> a-1 *)
  shows "(memR (flip_int_less_lower I) x) = (\<not>memL I x)" (* x \<notin> [a, b] *)
  using assms
  by (transfer') (simp)

lemma flip_int_less_lower_mem:
  assumes "\<not>bounded I" "\<not>mem I x" (* [a, \<infinity>], x < a *)
  shows "mem (flip_int_less_lower I) x" (* x \<in> [0, a-1] *)
  using assms
  by (transfer') (simp add: bounded_memR)

lemma int_flip_mem:
  assumes "bounded I" "mem I 0" "\<not>mem I x" (* [0, a], a<x *)
  shows "mem (flip_int I) x" (* [a, \<infinity>] *)
  using assms memL_mono
  by (transfer') (auto split: if_splits)

lemma flip_int_double_upper_leq:
  assumes "mem (flip_int_double_upper I) x" (* x \<in> [b+1, 2b] *)
  assumes "\<not> mem (flip_int_double_upper I) y" "y\<le>x" (* y \<notin> [b+1, 2b] and y \<le> x *)
  assumes "mem I 0"
  shows "mem I y"
proof -
  from assms(2) have "\<not>memL (flip_int_double_upper I) y \<or> \<not>memR (flip_int_double_upper I) y" by auto
  moreover have "\<forall>m. m \<le> x \<longrightarrow> memR (flip_int_double_upper I) m" using assms(1) by auto
  ultimately have "\<not>memL (flip_int_double_upper I) y" using assms(3) by auto
  then show "mem I y" using assms(4) by (transfer') (auto split: if_splits)
qed

lemma flip_int_double_upper_bounded[simp]: "bounded (flip_int_double_upper I) = bounded I"
  by (transfer') (auto)

lemma int_remove_lower_bound_bounded[simp]: "bounded (int_remove_lower_bound I) = bounded I"
  by (transfer') (auto)

lemma int_remove_lower_bound_mem: "mem I x \<Longrightarrow> mem (int_remove_lower_bound I) x"
  by (transfer') (auto)

lemma "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Since (Neg \<phi>) I (Neg \<psi>)))"
  by auto

lemma "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Until (Neg \<phi>) I (Neg \<psi>)))"
  by auto

definition release :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "release \<phi> I \<psi> = Neg (Until (Neg \<phi>) I (Neg \<psi>))"

lemma sat_release[simp]:
  "sat \<sigma> V v i (release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
  unfolding release_def
  by auto

lemma sat_release_eq[simp]: "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (release \<phi> I \<psi>)"
  by auto

definition once :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "once I \<phi> = Since TT I \<phi>"

lemma sat_once[simp] : "sat \<sigma> V v i (once I \<phi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: once_def)

lemma once_fvi[simp] : "fvi b (once I \<phi>) = fvi b \<phi>"
  by (auto simp: once_def)

definition historically :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically I \<phi> = (Neg (once I (Neg \<phi>)))"

lemma sat_historically[simp]: "sat \<sigma> V v i (historically I \<phi>) = (\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  unfolding historically_def
  by auto

(*lemma sat_historically_eq[simp]: "sat \<sigma> V v i (Historically I \<phi>) = sat \<sigma> V v i (historically I \<phi>)"
  by auto*)

definition eventually :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "eventually I \<phi> = Until TT I \<phi>"

lemma eventually_fvi[simp]: "fvi b (eventually I \<phi>) = fvi b \<phi>"
  by (auto simp: eventually_def)

lemma sat_eventually[simp]: "sat \<sigma> V v i (eventually I \<phi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: eventually_def)

definition always :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "always I \<phi> = (Neg (eventually I (Neg \<phi>)))"

(*lemma "sat \<sigma> V v i (Always I \<phi>) = sat \<sigma> V v i (Neg (eventually I (Neg \<phi>)))"
  by auto*)

lemma sat_always[simp]: "sat \<sigma> V v i (always I \<phi>) = (\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  unfolding always_def
  by auto

(*lemma sat_always_eq[simp]: "sat \<sigma> V v i (Always I \<phi>) = sat \<sigma> V v i (always I \<phi>)"
  by auto*)

(* case distrinction since intervals aren't allowed to be empty and flip_int [0, \<infinity>] would be *)
definition historically_safe_0 :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically_safe_0 I \<phi> = (if (bounded I) then (Or (Since \<phi> (flip_int I) (Next all \<phi>)) (Since \<phi> I (And first \<phi>))) else (Since \<phi> I (And first \<phi>)))"
                                                                                                        
definition historically_safe_unbounded :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically_safe_unbounded I \<phi> = (And (once (flip_int_less_lower I) (Prev all (Since \<phi> all (And \<phi> first)))) (once I \<phi>))"

definition historically_safe_bounded :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically_safe_bounded I \<phi> = (And (once I \<phi>) (Neg (once I (And (Or (once (int_remove_lower_bound I) \<phi>) (eventually (int_remove_lower_bound I) \<phi>)) (Neg \<phi>)))))"

definition always_safe_0 :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "always_safe_0 I \<phi> = (Or (Until \<phi> (flip_int_double_upper I) (Prev all \<phi>)) (Until \<phi> I (And \<phi> (Next (flip_int I) TT))))"

definition always_safe_bounded :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "always_safe_bounded I \<phi> = (And (eventually I \<phi>) (Neg (eventually I (And (Or (once (int_remove_lower_bound I) \<phi>) (eventually (int_remove_lower_bound I) \<phi>)) (Neg \<phi>)))))"

definition trigger_safe_0 :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "trigger_safe_0 \<phi> I \<psi> = Or (Since \<psi> I (And \<psi> \<phi>)) (historically_safe_0 I \<psi>)"

definition trigger_safe_unbounded :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "trigger_safe_unbounded \<phi> I \<psi> = And (once I TT) (Or (Or (historically_safe_unbounded I \<psi>) (once (flip_int_less_lower I) \<phi>)) (once (flip_int_less_lower I) (Prev all (Since \<psi> (int_remove_lower_bound I) (And \<phi> \<psi>)))))"

definition trigger_safe_bounded :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "trigger_safe_bounded \<phi> I \<psi> = And (once I TT) (Or (Or (historically_safe_bounded I \<psi>) (once (flip_int_less_lower I) \<phi>)) (once (flip_int_less_lower I) (Prev all (Since \<psi> (int_remove_lower_bound I) (And \<phi> \<psi>)))))"

definition and_trigger_safe_bounded :: "formula \<Rightarrow> formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "and_trigger_safe_bounded \<phi> \<phi>' I \<psi>' = (Or (And \<phi> (Neg (once I TT))) (And \<phi> (trigger_safe_bounded \<phi>' I \<psi>')))"

definition and_trigger_safe_unbounded :: "formula \<Rightarrow> formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "and_trigger_safe_unbounded \<phi> \<phi>' I \<psi>' = (Or (And \<phi> (Neg (once I TT))) (And \<phi> (trigger_safe_unbounded \<phi>' I \<psi>')))"

definition release_safe_0 :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "release_safe_0 \<phi> I \<psi> = Or (Until \<psi> I (And \<psi> \<phi>)) (always_safe_0 I \<psi>)"

definition release_safe_bounded :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "release_safe_bounded \<phi> I \<psi> = And (eventually I TT) (Or (Or (always_safe_bounded I \<psi>) (eventually (flip_int_less_lower I) \<phi>)) (eventually (flip_int_less_lower I) (Next all (Until \<psi> (int_remove_lower_bound I) (And \<psi> \<phi>)))))"

definition and_release_safe_bounded :: "formula \<Rightarrow> formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "and_release_safe_bounded \<phi> \<phi>' I \<psi>' = (Or (And \<phi> (Neg (eventually I TT))) (And \<phi> (release_safe_bounded \<phi>' I \<psi>')))"

lemma since_true:
  assumes "\<not>mem I 0"
  shows "sat \<sigma> V v i (Since \<phi> I TT) = sat \<sigma> V v i (Since \<phi> I (Next all \<phi>))"
proof (rule iffI)
  assume "sat \<sigma> V v i (Since \<phi> I TT)"
  then obtain j where j_props: "j\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" "\<forall>k\<in>{j<..i}. sat \<sigma> V v k \<phi>" by auto
  {
    assume "j=i"
    then have "False" using j_props assms by auto
  }
  then have "j<i" using j_props(1) using le_eq_less_or_eq by blast
  then show "sat \<sigma> V v i (Since \<phi> I (Next all \<phi>))"
    using j_props interval_all
    by (auto intro!: exI[of _ j])
next
  assume "sat \<sigma> V v i (Since \<phi> I (Next all \<phi>))"
  then show "sat \<sigma> V v i (Since \<phi> I TT)" by auto
qed

lemma until_true:
  assumes "\<not>mem I 0"
  shows "sat \<sigma> V v i (Until \<phi> I TT) = sat \<sigma> V v i (Until \<phi> I (Prev all \<phi>))"
proof (rule iffI)
  assume "sat \<sigma> V v i (Until \<phi> I TT)"
  then obtain j where j_props: "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. sat \<sigma> V v k \<phi>" by auto
  {
    assume "j=i"
    then have "False" using j_props assms by auto
  }
  then have "j>i" using j_props(1) using le_eq_less_or_eq by blast
  then show "sat \<sigma> V v i (Until \<phi> I (Prev all \<phi>))"
    using j_props interval_all
    by (auto split: nat.split intro!: exI[of _ j])
next
  assume "sat \<sigma> V v i (Until \<phi> I (Prev all \<phi>))"
  then show "sat \<sigma> V v i (Until \<phi> I TT)" by auto
qed

subsection \<open>Past-only formulas\<close>

fun past_only :: "formula \<Rightarrow> bool" where
  "past_only (Pred _ _) = True"
| "past_only (Eq _ _) = True"
| "past_only (Less _ _) = True"
| "past_only (LessEq _ _) = True"
| "past_only (Let _ \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Neg \<psi>) = past_only \<psi>"
| "past_only (Or \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (And \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Ands l) = (\<forall>\<alpha>\<in>set l. past_only \<alpha>)"
| "past_only (Exists \<psi>) = past_only \<psi>"
| "past_only (Agg _ _ _ _ \<psi>) = past_only \<psi>"
| "past_only (Prev _ \<psi>) = past_only \<psi>"
| "past_only (Next _ _) = False"
| "past_only (Since \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Until \<alpha> _ \<beta>) = False"
| "past_only (Trigger \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Release \<alpha> _ \<beta>) = False"
| "past_only (MatchP _ r) = Regex.pred_regex past_only r"
| "past_only (MatchF _ _) = False"

lemma past_only_sat:
  assumes "prefix_of \<pi> \<sigma>" "prefix_of \<pi> \<sigma>'"
  shows "i < plen \<pi> \<Longrightarrow> dom V = dom V' \<Longrightarrow>
     (\<And>p i. p \<in> dom V \<Longrightarrow> i < plen \<pi> \<Longrightarrow> the (V p) i = the (V' p) i) \<Longrightarrow>
     past_only \<phi> \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma>' V' v i \<phi>"
proof (induction \<phi> arbitrary: V V' v i)
  case (Pred e ts)
  show ?case proof (cases "V e")
    case None
    then have "V' e = None" using \<open>dom V = dom V'\<close> by auto
    with None \<Gamma>_prefix_conv[OF assms(1,2) Pred(1)] show ?thesis by simp
  next
    case (Some a)
    moreover obtain a' where "V' e = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    moreover have "the (V e) i = the (V' e) i"
      using Some Pred(1,3) by (fastforce intro: domI)
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  let ?V = "\<lambda>V \<sigma>. (V(p \<mapsto> \<lambda>i. {v. length v = nfv \<phi> \<and> sat \<sigma> V v i \<phi>}))"
  show ?case unfolding sat.simps proof (rule Let.IH(2))
    show "i < plen \<pi>" by fact
    from Let.prems show "past_only \<psi>" by simp
    from Let.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by (simp del: fun_upd_apply)
  next
    fix p' i
    assume *: "p' \<in> dom (?V V \<sigma>)" "i < plen \<pi>"
    show "the (?V V \<sigma> p') i = the (?V V' \<sigma>' p') i" proof (cases "p' = p")
      case True
      with Let \<open>i < plen \<pi>\<close> show ?thesis by auto
    next
      case False
      with * show ?thesis by (auto intro!: Let.prems(3))
    qed
  qed
next
  case (Ands l)
  with \<Gamma>_prefix_conv[OF assms] show ?case by simp
next
  case (Prev I \<phi>)
  with \<tau>_prefix_conv[OF assms] show ?case by (simp split: nat.split)
next
  case (Since \<phi>1 I \<phi>2)
  with \<tau>_prefix_conv[OF assms] show ?case by auto
next
  case (Trigger \<phi> I \<psi>)
  with \<tau>_prefix_conv[OF assms] show ?case by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) r a b = Regex.match (sat \<sigma>' V' v) r a b" if "b < plen \<pi>" for a b
    using that by (intro Regex.match_cong_strong) (auto simp: regex.pred_set)
  with \<tau>_prefix_conv[OF assms] MatchP(2) show ?case by auto
qed auto


subsection \<open>Safe formulas\<close>

fun remove_neg :: "formula \<Rightarrow> formula" where
  "remove_neg (Neg \<phi>) = \<phi>"
| "remove_neg \<phi> = \<phi>"

lemma fvi_remove_neg[simp]: "fvi b (remove_neg \<phi>) = fvi b \<phi>"
  by (cases \<phi>) simp_all

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

fun is_constraint :: "formula \<Rightarrow> bool" where
  "is_constraint (Eq t1 t2) = True"
| "is_constraint (Less t1 t2) = True"
| "is_constraint (LessEq t1 t2) = True"
| "is_constraint (Neg (Eq t1 t2)) = True"
| "is_constraint (Neg (Less t1 t2)) = True"
| "is_constraint (Neg (LessEq t1 t2)) = True"
| "is_constraint _ = False"

definition safe_assignment :: "nat set \<Rightarrow> formula \<Rightarrow> bool" where
  "safe_assignment X \<phi> = (case \<phi> of
       Eq (Var x) (Var y) \<Rightarrow> (x \<notin> X \<longleftrightarrow> y \<in> X)
     | Eq (Var x) t \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | Eq t (Var x) \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | _ \<Rightarrow> False)"

definition safe_formula_dual where "
  safe_formula_dual b safe_formula \<phi> I \<psi> = (if (mem I 0) then
    (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> (
      safe_formula \<phi> \<comment> \<open>\<or> safe_assignment (fv \<psi>) \<phi> \<or> is_constraint \<phi>\<close> \<or>
      (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)
    ))
      else
    b \<and> (safe_formula \<phi> \<and> safe_formula \<psi> \<and> fv \<phi> = fv \<psi>))
"

lemma safe_formula_dual_impl:
  assumes "\<forall>x. P x \<longrightarrow> Q x"
  shows "safe_formula_dual b P \<phi> I \<psi> \<Longrightarrow> safe_formula_dual b Q \<phi> I \<psi>"
  using assms unfolding safe_formula_dual_def by (auto split: if_splits formula.splits)

lemma size_regex_cong [fundef_cong]:
  assumes "\<And>f. size f < Regex.size_regex size r \<Longrightarrow> size' f = size'' f"
  shows "Regex.size_regex size' r = Regex.size_regex size'' r"
  using assms
  by (induction r) (auto)

fun size' :: "formula \<Rightarrow> nat" where
  "size' (Pred r ts) = 0"
| "size' (Let p \<phi> \<psi>) = size' \<psi> + size' \<phi> + 1"
| "size' (Eq t1 t2) = 0"
| "size' (Less t1 t2) = 0"
| "size' (LessEq t1 t2) = 0"
| "size' (Neg \<phi>) = size' \<phi> + 1"
| "size' (Or \<phi> \<psi>) = size' \<phi> + size' \<psi> + 1"
| "size' (And \<phi> \<psi>) = (case \<psi> of
    (Release \<phi>' I \<psi>') \<Rightarrow> 2 * size' \<phi> + 2 * size' \<psi> + 1
    | _ \<Rightarrow> size' \<phi> + size' \<psi> + 1
  )"
| "size' (Ands \<phi>s) = sum_list (map (size') \<phi>s) + 1"
| "size' (Exists \<phi>) = size' \<phi> + 1"
| "size' (Agg y \<omega> b' f \<phi>) = size' \<phi> + 1"
| "size' (Prev I \<phi>) = size' \<phi> + 1"
| "size' (Next I \<phi>) = size' \<phi> + 1"
| "size' (Since \<phi> I \<psi>) = size' \<phi> + size' \<psi> + 1"
| "size' (Until \<phi> I \<psi>) = size' \<phi> + size' \<psi> + 1"
| "size' (Trigger \<phi> I \<psi>) = size' \<phi> + size' \<psi> + 1"
| "size' (Release \<phi> I \<psi>) = 6 * size' \<phi> + 24 * size' \<psi> + 110"
| "size' (MatchF I r) = Regex.size_regex (size') r"
| "size' (MatchP I r) = Regex.size_regex (size') r"



lemma size'_and_release: "size' (And \<phi> (Release \<phi>' I \<psi>')) \<ge> size' (and_release_safe_bounded \<phi> \<phi>' I \<psi>') + 1"
  unfolding and_release_safe_bounded_def
  unfolding release_safe_bounded_def always_safe_bounded_def eventually_def once_def TT_def FF_def
  by (auto simp add: size'.simps(17) split: formula.splits)

lemma size'_Release: "size' (Release \<phi> I \<psi>) \<ge> size' (release_safe_0 \<phi> I \<psi>) + size' (release_safe_bounded \<phi> I \<psi>) + 1"
  unfolding release_safe_0_def release_safe_bounded_def always_safe_0_def always_safe_bounded_def eventually_def once_def TT_def FF_def
  by (auto simp add: size'.simps(17) split: formula.splits)

lemma size'_Or:
  "size' \<phi> < size' (And \<phi> \<psi>)"
  "size' \<psi> < size' (And \<phi> \<psi>)"
  by (auto split: formula.splits)

lemma size'_release_aux:
  "size' (and_release_safe_bounded \<phi> \<phi>' I \<psi>') < 221 + (2 * size' \<phi> + (12 * size' \<phi>' + 48 * size' \<psi>'))"
  "(case \<phi> of Release \<phi>' I \<psi>' \<Rightarrow> 2 * size' \<psi> + 2 * size' \<phi> + 1 | _ \<Rightarrow> size' \<psi> + size' \<phi> + 1) + size' (always_safe_0 I \<psi>) < 23 * size' \<psi> + (108 + 6 * size' \<phi>)"
  "size' (release_safe_bounded \<phi> I \<psi>) < 6 * size' \<phi> + 24 * size' \<psi> + 110"
  "size' (release_safe_0 \<phi> I \<psi>) < 6 * size' \<phi> + 24 * size' \<psi> + 110"
  unfolding and_release_safe_bounded_def release_safe_0_def release_safe_bounded_def always_safe_bounded_def always_safe_0_def eventually_def once_def TT_def FF_def
  by (auto split: formula.split)

lemma safe_formula_dual_size [fundef_cong]:
  assumes "\<And>f. size' f \<le> size' \<phi> + size' \<psi> \<Longrightarrow> safe_formula f = safe_formula' f"
  shows "safe_formula_dual b safe_formula \<phi> I \<psi> = safe_formula_dual b safe_formula' \<phi> I \<psi>"
  using assms
  by (auto simp add: safe_formula_dual_def split: formula.splits)

lemma sum_list_mem_leq:
  fixes f::"'a \<Rightarrow> nat"
  shows "x \<in> set l \<Longrightarrow> f x \<le> sum_list (map f l)"
  by (induction l) (auto)

lemma regex_atms_size': "x \<in> regex.atms r \<Longrightarrow> size' x < regex.size_regex size' r"
  by (induction r) (auto)

function (sequential) safe_formula :: "formula \<Rightarrow> bool" where
  "safe_formula (Eq t1 t2) = (is_Const t1 \<and> (is_Const t2 \<or> is_Var t2) \<or> is_Var t1 \<and> is_Const t2)"
| "safe_formula (Neg (Eq (Var x) (Var y))) = (x = y)"
| "safe_formula (Less t1 t2) = False"
| "safe_formula (LessEq t1 t2) = False"
| "safe_formula (Pred e ts) = (\<forall>t\<in>set ts. is_Var t \<or> is_Const t)"
| "safe_formula (Let p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Neg \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
| "safe_formula (Or \<phi> \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (And \<phi> \<psi>) = (safe_formula \<phi> \<and>
    (safe_assignment (fv \<phi>) \<psi> \<or> safe_formula \<psi> \<or>
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Neg \<psi>' \<Rightarrow> safe_formula \<psi>'
      | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
      | (Release \<phi>' I \<psi>') \<Rightarrow> (
        bounded I \<and> \<not>mem I 0 \<and>
        safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
        safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
      )
      | _ \<Rightarrow> False
    ))))"
| "safe_formula (Ands l) = (let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
    list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg \<and>
    \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))
  )"
| "safe_formula (Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Agg y \<omega> b f \<phi>) = (safe_formula \<phi> \<and> y + b \<notin> fv \<phi> \<and> {0..<b} \<subseteq> fv \<phi> \<and> fv_trm f \<subseteq> fv \<phi>)"
| "safe_formula (Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Since \<phi> I \<psi>) = (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"
| "safe_formula (Until \<phi> I \<psi>) = (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"
| "safe_formula (Trigger \<phi> I \<psi>) = safe_formula_dual False safe_formula \<phi> I \<psi>"
| "safe_formula (Release \<phi> I \<psi>) = (mem I 0 \<and> bounded I \<and> safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> safe_formula (release_safe_0 \<phi> I \<psi>))"
| "safe_formula (MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Past Strict r"
| "safe_formula (MatchF I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Futu Strict r"
  by pat_completeness auto
termination
  using size'_and_release size'_Release size'_Or size'_release_aux
  by (relation "measure size'")
  (auto simp add: Nat.less_Suc_eq_le release_safe_0_def dest!: sum_list_mem_leq[of _ _ size'] regex_atms_size')
  

lemma safe_abbrevs[simp]: "safe_formula TT" "safe_formula FF"
  unfolding TT_def FF_def by auto

lemma TT_future_bounded[simp]: "future_bounded TT"
  by (simp add: TT_def FF_def)

lemma first_fv[simp]: "fv first = {}"
  by (simp add: first_def)

lemma first_safe[simp]: "safe_formula first"
  by (simp add: first_def)

lemma first_future_bounded[simp]: "future_bounded first"
  by (simp add: first_def)

lemma once_fv[simp]: "fv (once I \<phi>) = fv \<phi>"
  by (simp add: once_def)

lemma once_safe[simp]: "safe_formula (once I \<phi>) = safe_formula \<phi>"
  by (simp add: once_def)

lemma once_future_bounded[simp]: "future_bounded (once I \<phi>) = future_bounded \<phi>"
  by (simp add: once_def)

lemma eventually_fv[simp]: "fv (eventually I \<phi>) = fv \<phi>"
  by (simp add: eventually_def)

lemma eventually_safe[simp]: "safe_formula (eventually I \<phi>) = safe_formula \<phi>"
  by (simp add: eventually_def)

lemma eventually_future_bounded[simp]: "future_bounded (eventually I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (simp add: eventually_def)

(* historically *)

(* [0, b] *)
lemma historically_safe_0_safe[simp]: "safe_formula (historically_safe_0 I \<phi>) = safe_formula \<phi>"
  apply (auto simp add: historically_safe_0_def safe_assignment_def split: formula.splits)
  subgoal for \<phi>
    by (cases \<phi>) (auto simp add: is_Const_def)
  subgoal for \<phi>
    by (cases \<phi>) (auto simp add: is_Const_def)
  done

lemma historically_safe_0_fv[simp]: "fv (historically_safe_0 I \<phi>) = fv \<phi>"
  by (auto simp add: historically_safe_0_def)

lemma historically_safe_0_future_bounded[simp]: "future_bounded (historically_safe_0 I \<phi>) = future_bounded \<phi>"
  by (simp add: historically_safe_0_def eventually_def)

(* [b, \<infinity>) *)

lemma historically_safe_unbounded_safe[simp]:"safe_formula (historically_safe_unbounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_unbounded_fv[simp]: "fv (historically_safe_unbounded I \<phi>) = fv \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_future_bounded[simp]:"future_bounded (historically_safe_unbounded I \<phi>) = future_bounded \<phi>"
  by (simp add: historically_safe_unbounded_def)

(* [a, b] *)

lemma historically_safe_bounded_safe[simp]: "safe_formula (historically_safe_bounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma historically_safe_bounded_fv[simp]: "fv (historically_safe_bounded I \<phi>) = fv \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma historically_safe_bounded_future_bounded[simp]: "future_bounded (historically_safe_bounded I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (auto simp add: historically_safe_bounded_def bounded.rep_eq int_remove_lower_bound.rep_eq)

(*lemma "mem I 0 \<Longrightarrow> safe_formula (historically I \<phi>) = safe_formula (historically_safe_0 I \<phi>)"
  unfolding historically_def once_def
  by auto

lemma "\<not>mem I 0 \<Longrightarrow> \<not>bounded I \<Longrightarrow> safe_formula (historically I \<phi>) = safe_formula (historically_safe_unbounded I \<phi>)"
  by auto

lemma "\<not>mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> safe_formula (historically I \<phi>) = safe_formula (historically_safe_bounded I \<phi>)"
  by auto*)

(* always *)

(* [0, b] *)

lemma always_safe_0_safe[simp]: "safe_formula (always_safe_0 I \<phi>) = safe_formula \<phi>"
  by (auto simp add: always_safe_0_def)

lemma always_safe_0_safe_fv[simp]: "fv (always_safe_0 I \<phi>) = fv \<phi>"
  by (auto simp add: always_safe_0_def)

lemma always_safe_0_future_bounded[simp]: "future_bounded (always_safe_0 I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (simp add: always_safe_0_def bounded.rep_eq flip_int_double_upper.rep_eq)

(* [a, b] *)

lemma always_safe_bounded_safe[simp]: "safe_formula (always_safe_bounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: always_safe_bounded_def)

lemma always_safe_bounded_fv[simp]: "fv (always_safe_bounded I \<phi>) = fv \<phi>"
  by (auto simp add: always_safe_bounded_def)

lemma always_safe_bounded_future_bounded[simp]: "future_bounded (always_safe_bounded I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (auto simp add: always_safe_bounded_def bounded.rep_eq int_remove_lower_bound.rep_eq)

(*lemma "mem I 0 \<Longrightarrow> safe_formula (always I \<phi>) = safe_formula (always_safe_0 I \<phi>)"
  by auto

lemma "\<not>mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> safe_formula (always I \<phi>) = safe_formula (always_safe_bounded I \<phi>)"
  by auto*)                        


lemma safe_formula_release_bounded:
  assumes "safe_formula \<phi> \<and> safe_formula \<psi> \<and> fv \<phi> = fv \<psi>"
  shows "safe_formula (release_safe_bounded \<phi> I \<psi>)"
  using assms
  by (auto simp add: release_safe_bounded_def once_def historically_safe_unbounded_def safe_formula_dual_def)

abbreviation "safe_regex \<equiv> Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
  (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"

lemma safe_regex_safe_formula:
  "safe_regex m g r \<Longrightarrow> \<phi> \<in> Regex.atms r \<Longrightarrow> safe_formula \<phi> \<or>
  (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi>)"
  by (cases g) (auto dest!: safe_regex_safe[rotated] split: formula.splits[where formula=\<phi>])

definition safe_neg :: "formula \<Rightarrow> bool" where
  "safe_neg \<phi> \<longleftrightarrow> (\<not> safe_formula \<phi> \<longrightarrow> (case \<phi> of (Neg \<phi>') \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))"

definition atms :: "formula Regex.regex \<Rightarrow> formula set" where
  "atms r = (\<Union>\<phi> \<in> Regex.atms r.
     if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"

lemma atms_simps[simp]:
  "atms (Regex.Skip n) = {}"
  "atms (Regex.Test \<phi>) = (if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
  "atms (Regex.Plus r s) = atms r \<union> atms s"
  "atms (Regex.Times r s) = atms r \<union> atms s"
  "atms (Regex.Star r) = atms r"
  unfolding atms_def by auto

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) (auto split: formula.splits)

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma release_safe_unbounded: "safe_formula (release_safe_bounded \<phi>' I \<psi>') \<Longrightarrow> safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>'"
  unfolding release_safe_bounded_def always_safe_bounded_def once_def eventually_def TT_def FF_def
  by (auto simp add: safe_assignment_def)

lemma safe_formula_induct[consumes 1, case_names Eq_Const Eq_Var1 Eq_Var2 neq_Var Pred Let
    And_assign And_safe And_constraint And_Not And_Trigger And_Release
    Ands Neg Or Exists Agg
    Prev Next
    Since Not_Since Until Not_Until
    Trigger_0 Trigger
    Release_0 Release
    MatchP MatchF]:
  assumes "safe_formula \<phi>"
    and Eq_Const: "\<And>c d. P (Eq (Const c) (Const d))"
    and Eq_Var1: "\<And>c x. P (Eq (Const c) (Var x))"
    and Eq_Var2: "\<And>c x. P (Eq (Var x) (Const c))"
    and neq_Var: "\<And>x. P (Neg (Eq (Var x) (Var x)))"
    and Pred: "\<And>e ts. \<forall>t\<in>set ts. is_Var t \<or> is_Const t \<Longrightarrow> P (Pred e ts)"
    and Let: "\<And>p \<phi> \<psi>. {0..<nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Let p \<phi> \<psi>)"
    and And_assign: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_safe: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow>
      P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_constraint: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> \<not> safe_formula \<psi> \<Longrightarrow>
      fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> is_constraint \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_Not: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) (Neg \<psi>) \<Longrightarrow> \<not> safe_formula (Neg \<psi>) \<Longrightarrow>
      fv (Neg \<psi>) \<subseteq> fv \<phi> \<Longrightarrow> \<not> is_constraint (Neg \<psi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> (Neg \<psi>))"
    and And_Trigger: "\<And>\<phi> \<phi>' I \<psi>'. safe_formula \<phi> \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' \<Longrightarrow> fv (Trigger \<phi>' I \<psi>') \<subseteq> fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<phi>' \<Longrightarrow> P \<psi>' \<Longrightarrow> P (And \<phi> (Trigger \<phi>' I \<psi>'))"
    and And_Release: "\<And>\<phi> \<phi>' I \<psi>'. safe_formula \<phi> \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> fv \<phi>' = fv \<psi>' \<Longrightarrow> bounded I \<Longrightarrow> \<not>mem I 0 \<Longrightarrow> fv (Release \<phi>' I \<psi>') \<subseteq> fv \<phi>  \<Longrightarrow> P (and_release_safe_bounded \<phi> \<phi>' I \<psi>') \<Longrightarrow> P \<phi> \<Longrightarrow> P \<phi>' \<Longrightarrow> P \<psi>' \<Longrightarrow> P (And \<phi> (Release \<phi>' I \<psi>'))"
    and Ands: "\<And>l pos neg. (pos, neg) = partition safe_formula l \<Longrightarrow> pos \<noteq> [] \<Longrightarrow>
      list_all safe_formula pos \<Longrightarrow> list_all (\<lambda>\<phi>. (case \<phi> of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | _ \<Rightarrow> safe_formula \<phi>
        )
      ) neg \<Longrightarrow>
      (\<Union>\<phi>\<in>set neg. fv \<phi>) \<subseteq> (\<Union>\<phi>\<in>set pos. fv \<phi>) \<Longrightarrow>
      list_all P pos \<Longrightarrow> list_all (\<lambda>\<phi>. (case \<phi> of
          Neg \<phi>' \<Rightarrow> P \<phi>'
          | _ \<Rightarrow> P \<phi>
        )
      ) neg \<Longrightarrow> P (Ands l)"
    and Neg: "\<And>\<phi>. fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Neg \<phi>)"
    and Or: "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Or \<phi> \<psi>)"
    and Exists: "\<And>\<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Exists \<phi>)"
    and Agg: "\<And>y \<omega> b f \<phi>. y + b \<notin> fv \<phi> \<Longrightarrow> {0..<b} \<subseteq> fv \<phi> \<Longrightarrow> fv_trm f \<subseteq> fv \<phi> \<Longrightarrow>
      safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Agg y \<omega> b f \<phi>)"
    and Prev: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Prev I \<phi>)"
    and Next: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Next I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since \<phi> I \<psi>)"
    and Not_Since: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since (Neg \<phi>) I \<psi> )"
    and Until: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until \<phi> I \<psi>)"
    and Not_Until: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until (Neg \<phi>) I \<psi>)"
    and Trigger_0: "\<And>\<phi> I \<psi>. mem I 0 \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> 
      ((safe_formula \<phi> \<and> P \<phi>) \<or> \<comment> \<open>(safe_assignment (fv \<psi>) \<phi>) \<or> is_constraint \<phi> \<or>\<close> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> P \<phi>' | _ \<Rightarrow> False)) \<Longrightarrow> P \<psi> \<Longrightarrow> P (Trigger \<phi> I \<psi>)"
    and Trigger: "\<And>\<phi> I \<psi>. False \<Longrightarrow> \<not>mem I 0 \<Longrightarrow> fv \<phi> = fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Trigger \<phi> I \<psi>)"
    and Release_0: "\<And>\<phi> I \<psi>. mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> P (release_safe_0 \<phi> I \<psi>) \<Longrightarrow> P (Release \<phi> I \<psi>)"
    and Release: "\<And>\<phi> I \<psi>. False \<Longrightarrow> \<not>mem I 0 \<Longrightarrow> fv \<phi> = fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Release \<phi> I \<psi>)"
    and MatchP: "\<And>I r. safe_regex Past Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchP I r)"
    and MatchF: "\<And>I r. safe_regex Futu Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchF I r)"
  shows "P \<phi>"
using assms(1) proof (induction \<phi> rule: safe_formula.induct)
  case (1 t1 t2)
  then show ?case using Eq_Const Eq_Var1 Eq_Var2 by (auto simp: trm.is_Const_def trm.is_Var_def)
next
  case (9 \<phi> \<psi>)
  from \<open>safe_formula (And \<phi> \<psi>)\<close> have "safe_formula \<phi>" by simp
  from \<open>safe_formula (And \<phi> \<psi>)\<close> consider
    (a) "safe_assignment (fv \<phi>) \<psi>"
    | (b) "\<not> safe_assignment (fv \<phi>) \<psi>" "safe_formula \<psi>"
    | (c) "fv \<psi> \<subseteq> fv \<phi>" "\<not> safe_assignment (fv \<phi>) \<psi>" "\<not> safe_formula \<psi>" "is_constraint \<psi>"
    | (d) \<psi>' where "fv \<psi> \<subseteq> fv \<phi>" "\<not> safe_assignment (fv \<phi>) \<psi>" "\<not> safe_formula \<psi>" "\<not> is_constraint \<psi>"
        "\<psi> = Neg \<psi>'" "safe_formula \<psi>'"
    | (e) \<phi>' I \<psi>' where "\<psi> = Trigger \<phi>' I \<psi>'" "safe_formula_dual True safe_formula \<phi>' I \<psi>'" "fv \<psi> \<subseteq> fv \<phi>"
    | (f) \<phi>' I \<psi>' where "\<psi> = Release \<phi>' I \<psi>'" "bounded I" "\<not>mem I 0" "safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')" "safe_formula \<phi>'" "safe_formula \<psi>'" "fv \<phi>' = fv \<psi>'" "fv \<psi> \<subseteq> fv \<phi>"
    by (cases \<psi>) (auto)
  then show ?case proof cases
    case a
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_assign)
  next
    case b
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_safe)
  next
    case c
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_constraint)
  next
    case d
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (auto intro!: And_Not)
  next
    case e
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close>
    proof (cases "safe_formula \<phi>'")
      case False
      then have mem: "mem I 0"
        using e False
        by (auto simp add: safe_formula_dual_def split: if_splits)
      then have safe_dual_mem_0: "safe_formula_dual False safe_formula \<phi>' I \<psi>'"
        using e
        unfolding safe_formula_dual_def
        by auto
      then have \<psi>_props:
        "\<not> safe_assignment (fv \<phi>) \<psi>"
        "safe_formula \<psi>"
        using e(1) safe_dual_mem_0
        unfolding safe_assignment_def
        by auto
      then show ?thesis
        using "9.IH"(1-2) \<open>safe_formula \<phi>\<close>
        by (auto intro!: And_safe)
    qed (auto intro!: And_Trigger simp add: safe_formula_dual_def split: if_splits formula.splits)
  next
    case f
    have p: "P \<phi>'" "P \<psi>'"
      using "9.IH"(5-6)[OF f(1)] f(5,6)
      by auto
    show ?thesis
      using And_Release[OF \<open>safe_formula \<phi>\<close> f(5-7, 2-3) f(8)[unfolded f(1)] _ _ p] "9.IH"(1)[OF \<open>safe_formula \<phi>\<close>] "9.IH"(7)[OF f(1,4)] f(1)
      by auto
  qed
next
  case (10 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "pos \<noteq> []" using "10.prems" posneg by simp
  moreover have "list_all safe_formula pos" using posneg by (simp add: list.pred_set)
  moreover have neg_props: "\<forall>\<phi> \<in> set neg. ((case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    )"
    using "10.prems" posneg
    by (simp add: list.pred_set)
  moreover have "list_all P pos"
    using posneg "10.IH"(1) by (simp add: list_all_iff)
  moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
          Neg \<phi>' \<Rightarrow> P \<phi>'
          | _ \<Rightarrow> P \<phi>
        )
      ) neg"
  proof -
    {
      fix \<phi>
      assume assm: "\<phi> \<in> set neg"
      then have \<phi>_props: "case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> safe_formula \<phi>"
        using neg_props
        by blast
      
      have "(case \<phi> of
          Neg \<phi>' \<Rightarrow> P \<phi>'
          | _ \<Rightarrow> P \<phi>
        )"
      using "10.IH"(2-)[OF posneg _ assm] \<phi>_props
      by (cases \<phi>) (auto split: formula.splits)
    }
    then show ?thesis
      by (metis (no_types, lifting) Ball_set_list_all)
  qed
  ultimately show ?case using "10.prems" Ands posneg by simp
next
  case (15 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "15.IH"(1-2) "15.prems" Since by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: Since Not_Since) (*SLOW*)
next
  case (16 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "16.IH"(1-2)"16.prems" Until by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: Until Not_Until) (*SLOW*)
next
  case (17 \<phi> I \<psi>)
  then show ?case
  proof (cases "mem I 0")
    case mem: True
    show ?thesis
    proof (cases "case \<phi> of Neg x \<Rightarrow> safe_formula x | _ \<Rightarrow> False")
      case True
      then obtain \<phi>' where "\<phi> = Neg \<phi>'"
        by (auto split: formula.splits)
      then show ?thesis using mem 17 Trigger_0 by (auto simp add: safe_formula_dual_def)
    next
      case False
      then show ?thesis using mem 17 Trigger_0 by (auto simp add: safe_formula_dual_def)
    qed
  next
    case False
    then show ?thesis using Trigger 17 by (auto simp add: safe_formula_dual_def)
  qed
next
  case (18 \<phi> I \<psi>)
  then show ?case
  proof (cases "mem I 0")
    case mem: True
    show ?thesis using 18 Release_0 by auto
  next
    case False
    then show ?thesis using Release 18 by (auto simp add: safe_formula_dual_def)
  qed
next
  case (19 I r)
  then show ?case
    by (intro MatchP) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
next
  case (20 I r)
  then show ?case
    by (intro MatchF) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
qed (auto simp: assms)

lemma safe_formula_Neg: "safe_formula (Formula.Neg \<phi>) = ((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>))"
  by (induct "Formula.Neg \<phi>" rule: safe_formula.induct) auto

subsection \<open>Slicing traces\<close>

qualified fun matches ::
  "env \<Rightarrow> formula \<Rightarrow> name \<times> event_data list \<Rightarrow> bool" where
  "matches v (Pred r ts) e = (fst e = r \<and> map (eval_trm v) ts = snd e)"
| "matches v (Let p \<phi> \<psi>) e =
    ((\<exists>v'. matches v' \<phi> e \<and> matches v \<psi> (p, v')) \<or>
    fst e \<noteq> p \<and> matches v \<psi> e)"
| "matches v (Eq _ _) e = False"
| "matches v (Less _ _) e = False"
| "matches v (LessEq _ _) e = False"
| "matches v (Neg \<phi>) e = matches v \<phi> e"
| "matches v (Or \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (And \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Ands l) e = (\<exists>\<phi>\<in>set l. matches v \<phi> e)"
| "matches v (Exists \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Agg y \<omega> b f \<phi>) e = (\<exists>zs. length zs = b \<and> matches (zs @ v) \<phi> e)"
| "matches v (Prev I \<phi>) e = matches v \<phi> e"
| "matches v (Next I \<phi>) e = matches v \<phi> e"
| "matches v (Since \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Until \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Trigger \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Release \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (MatchP I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (MatchF I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"

lemma matches_cong:
  "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v' e)
  case (Pred n ts)
  show ?case
    by (simp cong: map_cong eval_trm_fv_cong[OF Pred(1)[simplified, THEN bspec]])
next
  case (Let p b \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> (set l) \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
  proof -
    fix \<phi> assume "\<phi> \<in> (set l)"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "matches v \<phi> e = matches v' \<phi> e" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case by simp
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "matches (zs @ v) \<phi> e = matches (zs @ v') \<phi> e" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  then show ?case by auto
qed (auto 9 0 simp add: nth_Cons' fv_regex_alt)

abbreviation relevant_events where "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

lemma sat_slice_strong:
  assumes "v \<in> S" "dom V = dom V'"
    "\<And>p v i. p \<in> dom V \<Longrightarrow> (p, v) \<in> relevant_events \<phi> S \<Longrightarrow> v \<in> the (V p) i \<longleftrightarrow> v \<in> the (V' p) i"
  shows "relevant_events \<phi> S - {e. fst e \<in> dom V} \<subseteq> E \<Longrightarrow>
    sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  using assms
proof (induction \<phi> arbitrary: V V' v S i)
  case (Pred r ts)
  show ?case proof (cases "V r")
    case None
    then have "V' r = None" using \<open>dom V = dom V'\<close> by auto
    with None Pred(1,2) show ?thesis by (auto simp: domIff dest!: subsetD)
  next
    case (Some a)
    moreover obtain a' where "V' r = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    moreover have "(map (eval_trm v) ts \<in> the (V r) i) = (map (eval_trm v) ts \<in> the (V' r) i)"
      using Some Pred(2,4) by (fastforce intro: domI)
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  from Let.prems show ?case unfolding sat.simps
  proof (intro Let(2)[of S], goal_cases relevant v dom V)
    case (V p' v' i)
    then show ?case
    proof (cases "p' = p")
      case [simp]: True
      with V show ?thesis
        unfolding fun_upd_apply eqTrueI[OF True] if_True option.sel mem_Collect_eq
      proof (intro ex_cong conj_cong refl Let(1)[where
        S="{v'. (\<exists>v \<in> S. matches v \<psi> (p, v'))}" and V=V],
        goal_cases relevant' v' dom' V')
        case relevant'
        then show ?case
          by (elim subset_trans[rotated]) (auto simp: set_eq_iff)
      next
        case (V' p' v' i)
        then show ?case
          by (intro V(4)) (auto simp: set_eq_iff)
      qed auto
    next
      case False
      with V(2,3,5,6) show ?thesis
        unfolding fun_upd_apply eq_False[THEN iffD2, OF False] if_False
        by (intro V(4)) (auto simp: False)
    qed
  qed (auto simp: dom_def)
next
  case (Or \<phi> \<psi>)
  show ?case using Or.IH[of S V v V'] Or.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (And \<phi> \<psi>)
  show ?case using And.IH[of S V v V'] And.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Ands l)
  obtain "relevant_events (Ands l) S - {e. fst e \<in> dom V} \<subseteq> E" "v \<in> S" using Ands.prems(1) Ands.prems(2) by blast
  then have "{e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}} - {e. fst e \<in> dom V} \<subseteq> E" by simp
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    have "relevant_events \<phi> S = {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}" by simp
    have "{e. S \<inter> {v. matches v \<phi> e} \<noteq> {}} \<subseteq> {e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}}" (is "?A \<subseteq> ?B")
    proof (rule subsetI)
      fix e assume "e \<in> ?A"
      then have "S \<inter> {v. matches v \<phi> e} \<noteq> {}" by blast
      moreover have "S \<inter> {v. matches v (Ands l) e} \<noteq> {}"
      proof -
        obtain v where "v \<in> S" "matches v \<phi> e" using calculation by blast
        then show ?thesis using \<open>\<phi> \<in> set l\<close> by auto
      qed
      then show "e \<in> ?B" by blast
    qed
    then have "relevant_events \<phi> S - {e. fst e \<in> dom V} \<subseteq> E" using Ands.prems(1) by auto
    then show "sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
      using Ands.prems(2,3) \<open>\<phi> \<in> set l\<close>
      by (intro Ands.IH[of \<phi> S V v V' i] Ands.prems(4)) auto
  qed
  show ?case using \<open>\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>\<close> sat_Ands by blast
next
  case (Exists \<phi>)
  have "sat \<sigma> V (z # v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (z # v) i \<phi>" for z
    using Exists.prems(1-3) by (intro Exists.IH[where S="{z # v | v. v \<in> S}"] Exists.prems(4)) auto
  then show ?case by simp
next
  case (Agg y \<omega> b f \<phi>)
  have "sat \<sigma> V (zs @ v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (zs @ v) i \<phi>" if "length zs = b" for zs
    using that Agg.prems(1-3) by (intro Agg.IH[where S="{zs @ v | v. v \<in> S}"] Agg.prems(4)) auto
  then show ?case by (simp cong: conj_cong)
next
  case (Prev I \<phi>)
  then show ?case by (auto cong: nat.case_cong)
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  show ?case using Since.IH[of S V] Since.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Until \<phi> I \<psi>)
  show ?case using Until.IH[of S V] Until.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Trigger \<phi> I \<psi>)
  show ?case using Trigger.IH[of S V] Trigger.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Release \<phi> I \<psi>)
  show ?case using Release.IH[of S V] Release.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (MatchP I r)
  from MatchP.prems(1-3) have "Regex.match (sat \<sigma> V v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchP(1)[of _ S V v] MatchP.prems(4)) auto
  then show ?case
    by auto
next
  case (MatchF I r)
  from MatchF.prems(1-3) have "Regex.match (sat \<sigma> V v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchF(1)[of _ S V v] MatchF.prems(4)) auto
  then show ?case
    by auto
qed simp_all


subsection \<open>Translation to n-ary conjunction\<close>

fun get_and_list :: "formula \<Rightarrow> formula list" where
  "get_and_list (Ands l) = l"
| "get_and_list \<phi> = [\<phi>]"

lemma fv_get_and: "(\<Union>x\<in>(set (get_and_list \<phi>)). fvi b x) = fvi b \<phi>"
  by (induction \<phi> rule: get_and_list.induct) simp_all

lemma safe_get_and: "safe_formula \<phi> \<Longrightarrow> list_all safe_neg (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  then have l_props: "\<forall>\<phi> \<in> set l. \<not>safe_formula \<phi> \<longrightarrow> (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )"
    by (simp add: o_def list_all_iff)
  have "\<forall>\<phi> \<in> set l. \<not>safe_formula \<phi> \<longrightarrow> (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> False
      )"
  proof -
    {
      fix \<phi>
      assume "\<phi> \<in> set l" "\<not>safe_formula \<phi>"
      then have "(case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> False
      )"
        using l_props
        by (auto split: formula.splits)
    }
    then show ?thesis by auto
  qed
  then show ?case
    by (auto simp add: safe_neg_def list_all_iff)
qed (auto simp add: safe_neg_def list_all_iff )

lemma sat_get_and: "sat \<sigma> V v i \<phi> \<longleftrightarrow> list_all (sat \<sigma> V v i) (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: list_all_iff)

function (sequential) convert_multiway :: "formula \<Rightarrow> formula" where
  "convert_multiway (Pred p ts) = (Pred p ts)"
| "convert_multiway (Eq t u) = (Eq t u)"
| "convert_multiway (Less t u) = (Less t u)"
| "convert_multiway (LessEq t u) = (LessEq t u)"
| "convert_multiway (Let p \<phi> \<psi>) = Let p (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (Neg \<phi>) = Neg (convert_multiway \<phi>)"
| "convert_multiway (Or \<phi> \<psi>) = Or (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      And (convert_multiway \<phi>) \<psi>
    else if safe_formula \<psi> then
      Ands (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway \<psi>))
    else if (is_constraint \<psi>) then
      And (convert_multiway \<phi>) \<psi>
    else if (case \<psi> of (Trigger \<phi>' I \<psi>') \<Rightarrow> True | _ \<Rightarrow> False) then
      And (convert_multiway \<phi>) (convert_multiway \<psi>)
    else if (case \<psi> of (Release \<phi>' I \<psi>') \<Rightarrow> True | _ \<Rightarrow> False) then (
      case \<psi> of (Release \<phi>' I \<psi>') \<Rightarrow>
        if mem I 0 then
          And (convert_multiway \<phi>) (convert_multiway \<psi>)
        else
          convert_multiway (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
    )
    else Ands (convert_multiway \<psi> # get_and_list (convert_multiway \<phi>)))"
| "convert_multiway (Ands \<phi>s) = Ands (map convert_multiway \<phi>s)"
| "convert_multiway (Exists \<phi>) = Exists (convert_multiway \<phi>)"
| "convert_multiway (Agg y \<omega> b f \<phi>) = Agg y \<omega> b f (convert_multiway \<phi>)"
| "convert_multiway (Prev I \<phi>) = Prev I (convert_multiway \<phi>)"
| "convert_multiway (Next I \<phi>) = Next I (convert_multiway \<phi>)"
| "convert_multiway (Since \<phi> I \<psi>) = Since (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (Until \<phi> I \<psi>) = Until (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (Trigger \<phi> I \<psi>) = Trigger (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (Release \<phi> I \<psi>) = (
    if mem I 0 then
      convert_multiway (release_safe_0 \<phi> I \<psi>)
    else (
      convert_multiway (release_safe_bounded \<phi> I \<psi>)
    )
  )"
| "convert_multiway (MatchP I r) = MatchP I (Regex.map_regex convert_multiway r)"
| "convert_multiway (MatchF I r) = MatchF I (Regex.map_regex convert_multiway r)"
  by pat_completeness auto
termination
  using size'_and_release size'_Release size'_Or size'_release_aux
  apply (relation "measure size'")
  by (auto simp add: Nat.less_Suc_eq_le dest!: sum_list_mem_leq[of _ _ size'] regex_atms_size')

abbreviation "convert_multiway_regex \<equiv> Regex.map_regex convert_multiway"

lemma fv_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> fv \<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list \<phi>))). fv x)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "get_and_list (Ands l) = l" by simp
  have sub: "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)" using "1.prems" posneg by simp
  then have "fv (Ands l) \<subseteq> (\<Union>x\<in>set pos. fv x)"
  proof -
    have "fv (Ands l) = (\<Union>x\<in>set pos. fv x) \<union> (\<Union>x\<in>set neg. fv x)" using posneg by auto
    then show ?thesis using sub by simp
  qed
  then show ?case using posneg by auto
qed auto

lemma ex_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_ex safe_formula (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  have "get_and_list (Ands l) = l" by simp
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  then have "pos \<noteq> []" using "1.prems" by simp
  then obtain x where "x \<in> set pos" by fastforce
  then show ?case using posneg using Bex_set_list_ex by fastforce
qed simp_all

lemma case_NegE: "(case \<phi> of Neg \<phi>' \<Rightarrow> P \<phi>' | _ \<Rightarrow> False) \<Longrightarrow> (\<And>\<phi>'. \<phi> = Neg \<phi>' \<Longrightarrow> P \<phi>' \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (cases \<phi>) simp_all

declare fvi.simps(17) [simp del]

lemma release_fvi:
  "fvi b (Release \<phi> I \<psi>) = fvi b (release_safe_0 \<phi> I \<psi>)"
  "fvi b (Release \<phi> I \<psi>) = fvi b (release_safe_bounded \<phi> I \<psi>)"
  "fvi b (And \<phi>' (Release \<phi> I \<psi>)) = fvi b (and_release_safe_bounded \<phi>' \<phi> I \<psi>)"
  by (auto simp add: release_safe_0_def always_safe_0_def TT_def FF_def and_release_safe_bounded_def release_safe_bounded_def always_safe_bounded_def fvi.simps(17))

lemma convert_multiway_remove_neg: "safe_formula (remove_neg \<phi>) \<Longrightarrow> convert_multiway (remove_neg \<phi>) = remove_neg (convert_multiway \<phi>)"
proof (cases \<phi>)
  case (And \<phi>' \<psi>')
  then show ?thesis
    by (auto simp add: and_release_safe_bounded_def split: formula.splits)
qed (auto elim: case_NegE simp add: release_safe_0_def )
                    

lemma regex_atms_to_atms:
  assumes "safe_regex m s r"
  assumes "\<phi> \<in> regex.atms r"
  shows "\<phi> \<in> atms r \<or> (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi> \<and> \<psi> \<in> atms r)"
proof (cases "safe_formula \<phi>")
  case True
  then show ?thesis
    using assms(2)
    unfolding atms_def
    by auto
next
  case False
  then obtain \<psi> where \<psi>_props: "\<phi> = Neg \<psi>" "safe_formula \<psi>"
    using safe_regex_safe_formula[OF assms(1-2)]
    by auto
  have "(if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) = {\<psi>}"
    using False \<psi>_props(1)
    by auto
  then have "\<psi> \<in> atms r"
    using assms(2)
    unfolding atms_def
    by blast
  then have "\<phi> = Neg \<psi> \<and> safe_formula \<psi> \<and> \<psi> \<in> atms r"
    using \<psi>_props
    by auto
  then show ?thesis
    by auto
qed

lemma fv_convert_multiway_TT[simp]: "fvi b (convert_multiway TT) = {}"
  unfolding TT_def FF_def
  by auto

lemma fv_convert_multiway: "safe_formula \<phi> \<Longrightarrow> fvi b (convert_multiway \<phi>) = fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  then show ?case by (cases \<psi>) (auto simp: fv_get_and Un_commute)
next
  case (And_Not \<phi> \<psi>)
  then show ?case by (cases \<psi>) (auto simp: fv_get_and Un_commute)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  then show ?case by (auto simp: fv_get_and Un_commute safe_formula_dual_def)
next
  case (And_Release \<phi> \<phi>' I \<psi>')

  have unsafe_assignment: "\<not>safe_assignment (fv \<phi>) (Release \<phi>' I \<psi>')"
    unfolding safe_assignment_def
    by auto
  have unsafe: "\<not> safe_formula (Release \<phi>' I \<psi>')"
    using And_Release(6)
    unfolding safe_formula.simps
    by auto

  have "convert_multiway (And \<phi> (Release \<phi>' I \<psi>')) = convert_multiway (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
    using unsafe_assignment unsafe And_Release(6)
    by auto
  then have "fvi b (convert_multiway (And \<phi> (Release \<phi>' I \<psi>'))) = fvi b (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
    using And_Release.IH(1)
    by auto
  then show ?case
    using release_fvi(3)
    by auto
next
  case (Ands l pos neg)
  
  have neg_props: "\<And>\<phi>. \<phi>\<in>set neg \<Longrightarrow> \<forall>x. fvi x (convert_multiway \<phi>) = fvi x \<phi>"
  proof -
    fix \<phi>
    assume "\<phi> \<in> set neg"
    then have "case \<phi> of Neg \<phi>' \<Rightarrow> \<forall>x. fvi x (convert_multiway \<phi>') = fvi x \<phi>' | _ \<Rightarrow> \<forall>x. fvi x (convert_multiway \<phi>) = fvi x \<phi>"
      using Ands(7)
      unfolding list_all_iff
      by auto
    then show "\<forall>x. fvi x (convert_multiway \<phi>) = fvi x \<phi>"
      by (cases \<phi>) (auto)
  qed

  {
    fix \<phi>
    assume assm: "\<phi> \<in> set l"
    then have "\<phi> \<in> set pos \<or> \<phi> \<in> set neg"
      using Ands(1)
      by auto
    then have "fvi b \<phi> = fvi b (convert_multiway \<phi>)"
      using Ands(6) neg_props
      unfolding list_all_iff
      by auto
  }
  then show ?case by auto
next
  case (Trigger_0 \<phi> I \<psi>)
  have "\<forall>x. fvi x (convert_multiway \<phi>) = fvi x \<phi>"
    using Trigger_0(4)
    by (cases \<phi>) (auto)
  then show ?case
    using Trigger_0(5)
    by auto
next
  case (Release_0 \<phi> I \<psi>)
  then show ?case using release_fvi(1) by auto
next
  case (MatchP I r)

  have "(\<Union>x\<in>regex.atms r. fvi b (convert_multiway x)) = \<Union> (fvi b ` regex.atms r)"
  proof -
    {
      fix v
      assume "v \<in> (\<Union>x\<in>regex.atms r. fvi b (convert_multiway x))"
      then obtain \<phi> where \<phi>_props: "\<phi> \<in> regex.atms r" "v \<in> fvi b (convert_multiway \<phi>)"
        by blast
      have "\<phi> \<in> atms r \<or> (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi> \<and> \<psi> \<in> atms r)"
        using regex_atms_to_atms[OF MatchP(1) \<phi>_props(1)]
        by auto
      then have "\<forall>x. fvi x (convert_multiway \<phi>) = fvi x \<phi>"
        using MatchP(2)
        by auto
      then have "v \<in> (\<Union> (fvi b ` regex.atms r))"
        using \<phi>_props(1-2)
        by auto
    }
    moreover {
      fix v
      assume "v \<in> (\<Union> (fvi b ` regex.atms r))"
      then obtain \<phi> where \<phi>_props: "\<phi> \<in> regex.atms r" "v \<in> fvi b \<phi>"
        by blast
      have "\<phi> \<in> atms r \<or> (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi> \<and> \<psi> \<in> atms r)"
        using regex_atms_to_atms[OF MatchP(1) \<phi>_props(1)]
        by auto
      then have "\<forall>x. fvi x (convert_multiway \<phi>) = fvi x \<phi>"
        using MatchP(2)
        by auto
      then have "v \<in> (\<Union>x\<in>regex.atms r. fvi b (convert_multiway x))"
        using \<phi>_props(1-2)
        by auto
    }
    ultimately show ?thesis by blast
  qed
  then show ?case
    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by auto
next
  case (MatchF I r)
  have "(\<Union>x\<in>regex.atms r. fvi b (convert_multiway x)) = \<Union> (fvi b ` regex.atms r)"
  proof -
    {
      fix v
      assume "v \<in> (\<Union>x\<in>regex.atms r. fvi b (convert_multiway x))"
      then obtain \<phi> where \<phi>_props: "\<phi> \<in> regex.atms r" "v \<in> fvi b (convert_multiway \<phi>)"
        by blast
      have "\<phi> \<in> atms r \<or> (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi> \<and> \<psi> \<in> atms r)"
        using regex_atms_to_atms[OF MatchF(1) \<phi>_props(1)]
        by auto
      then have "\<forall>x. fvi x (convert_multiway \<phi>) = fvi x \<phi>"
        using MatchF(2)
        by auto
      then have "v \<in> (\<Union> (fvi b ` regex.atms r))"
        using \<phi>_props(1-2)
        by auto
    }
    moreover {
      fix v
      assume "v \<in> (\<Union> (fvi b ` regex.atms r))"
      then obtain \<phi> where \<phi>_props: "\<phi> \<in> regex.atms r" "v \<in> fvi b \<phi>"
        by blast
      have "\<phi> \<in> atms r \<or> (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi> \<and> \<psi> \<in> atms r)"
        using regex_atms_to_atms[OF MatchF(1) \<phi>_props(1)]
        by auto
      then have "\<forall>x. fvi x (convert_multiway \<phi>) = fvi x \<phi>"
        using MatchF(2)
        by auto
      then have "v \<in> (\<Union>x\<in>regex.atms r. fvi b (convert_multiway x))"
        using \<phi>_props(1-2)
        by auto
    }
    ultimately show ?thesis by blast
  qed
  then show ?case
    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by auto
qed (auto)

lemma nfv_convert_multiway: "safe_formula \<phi> \<Longrightarrow> nfv (convert_multiway \<phi>) = nfv \<phi>"
  unfolding nfv_def by (auto simp: fv_convert_multiway)

lemma get_and_nonempty:
  assumes "safe_formula \<phi>"
  shows "get_and_list \<phi> \<noteq> []"
  using assms by (induction \<phi>) auto

lemma future_bounded_get_and:
  "list_all future_bounded (get_and_list \<phi>) = future_bounded \<phi>"
  by (induction \<phi>) simp_all

lemma safe_convert_multiway: "safe_formula \<phi> \<Longrightarrow> safe_formula (convert_multiway \<phi>)"
proof (induction \<phi> rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  show ?case proof -
    let ?l = "get_and_list ?c\<phi> @ get_and_list ?c\<psi>"
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    have lsafe_neg: "list_all safe_neg ?l"
      using And_safe \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
      by (simp add: safe_get_and)
    have list_all_neg: "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
    proof -
      have "\<And>x. x \<in> set neg \<Longrightarrow> (case x of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula x
      )"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by auto
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "(case x of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | _ \<Rightarrow> safe_formula x
        )"
          unfolding safe_neg_def
          by (cases x) (auto)
      qed
      then show ?thesis by (auto simp: list_all_iff)
    qed

    have pos_filter: "pos = filter safe_formula (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
      using posneg by simp
    have "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)"
    proof -
      have 1: "fv ?c\<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<phi>))). fv x)" (is "_ \<subseteq> ?fv\<phi>")
        using And_safe \<open>safe_formula \<phi>\<close> by (blast intro!: fv_safe_get_and)
      have 2: "fv ?c\<psi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<psi>))). fv x)" (is "_ \<subseteq> ?fv\<psi>")
        using And_safe \<open>safe_formula \<psi>\<close> by (blast intro!: fv_safe_get_and)
      have "(\<Union>x\<in>set neg. fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>" proof -
        have "\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` (set pos \<union> set neg))"
          by simp
        also have "... \<subseteq> fv (convert_multiway \<phi>) \<union> fv (convert_multiway \<psi>)"
          unfolding partition_set[OF posneg[symmetric], simplified]
          by (simp add: fv_get_and)
        finally show ?thesis .
      qed
      then have "(\<Union>x\<in>set neg. fv x) \<subseteq> ?fv\<phi> \<union> ?fv\<psi>" using 1 2 by blast
      then show ?thesis unfolding pos_filter by simp
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_safe \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> list_all_neg \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  show ?case proof -
    let ?l = "Neg ?c\<psi> # get_and_list ?c\<phi>"
    note \<open>safe_formula ?c\<phi>\<close>
    then have "list_all safe_neg (get_and_list ?c\<phi>)" by (simp add: safe_get_and)
    moreover have "safe_neg (Neg ?c\<psi>)"
      using \<open>safe_formula ?c\<psi>\<close> by (simp add: safe_neg_def)
    then have lsafe_neg: "list_all safe_neg ?l" using calculation by simp
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    
    have list_all_neg: "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
    proof -
      have "\<And>x. x \<in> (set neg) \<Longrightarrow> (case x of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula x
      )"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by (auto simp del: filter.simps)
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "(case x of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | _ \<Rightarrow> safe_formula x
        )" unfolding safe_neg_def
          by presburger
      qed
      then show ?thesis using Ball_set_list_all by force
    qed

    have pos_filter: "pos = filter safe_formula ?l"
      using posneg by simp
    have neg_filter: "neg = filter (Not \<circ> safe_formula) ?l"
      using posneg by simp
    have "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set pos). fv x)"
    proof -
      have fv_neg: "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set ?l). fv x)" using posneg by auto
      have "(\<Union>x\<in>(set ?l). fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
        by (simp add: fv_get_and fv_convert_multiway)
      also have "fv ?c\<phi> \<union> fv ?c\<psi> \<subseteq> fv ?c\<phi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close> \<open>fv (Neg \<psi>) \<subseteq> fv \<phi>\<close>
        by (auto simp add: fv_convert_multiway)
      finally have "(\<Union>x\<in>(set neg). fv x) \<subseteq> fv ?c\<phi>"
        using fv_neg unfolding neg_filter by blast
      then show ?thesis
        unfolding pos_filter
        using fv_safe_get_and[OF And_Not.IH(1)]
        by auto
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_Not.IH \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> list_all_neg \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Trigger \<phi>' I \<psi>'"
  define f where "f = And \<phi> t"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have "\<exists>f \<in> set (get_and_list (convert_multiway \<phi>)). safe_formula f"
  proof -
    {
      assume assm: "\<forall>f \<in> set (get_and_list (convert_multiway \<phi>)). \<not>safe_formula f"
      then have "False"
      proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
        case True
        then obtain l where "convert_multiway \<phi> = Ands l"
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Trigger(5)
          by auto
      next
        case False
        then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
          using assm
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Trigger(5)
          by auto
      qed
    }
    then show ?thesis by auto
  qed
  then have filter_pos: "filter safe_formula (get_and_list (convert_multiway \<phi>)) \<noteq> []"
    by (simp add: filter_empty_conv)

  have \<phi>_fvs: "\<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>)))))) \<subseteq> \<Union>(set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
    using And_Trigger
    by (cases "(convert_multiway \<phi>)") (auto)

  show ?case
  proof (cases "safe_formula t")
    define l where "l = get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t)"
    define pos where "pos = fst (partition safe_formula l)"
    define neg where "neg = snd (partition safe_formula l)"

    case True
    then have convert_f: "convert_multiway f = Ands l"
      unfolding f_def l_def
      using t_not_safe_assign
      by auto

    have "safe_formula (convert_multiway t)"
      using And_Trigger True
      unfolding t_def
      by (auto split: if_splits simp add: safe_formula_dual_def fv_convert_multiway)
    then have neg_fv: "\<Union>(set (map fv neg)) = \<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      unfolding neg_def l_def t_def
      by auto

    have mem:
      "mem I 0"
      "safe_formula \<psi>'"
      "fv \<phi>' \<subseteq> fv \<psi>'"
      "safe_formula \<phi>'"
      using True And_Trigger
      unfolding t_def
      by (auto split: if_splits simp add: safe_formula_dual_def)

    have "filter safe_formula pos \<noteq> []"
      using filter_pos
      unfolding pos_def l_def
      by auto
    moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
      using And_Trigger mem
      unfolding l_def neg_def t_def
      by (cases "(convert_multiway \<phi>)") (auto simp add: safe_formula_dual_def fv_convert_multiway)
    moreover have "\<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))"
      using \<phi>_fvs neg_fv
      unfolding l_def pos_def
      by (auto simp add: fv_convert_multiway)
    ultimately have "safe_formula (Ands l)"
      unfolding pos_def neg_def
      by auto
    then show ?thesis
      using convert_f
      unfolding f_def t_def
      by auto
  next

    case False
    then have convert_f: "convert_multiway f = And (convert_multiway \<phi>) (Trigger (convert_multiway \<phi>') I (convert_multiway \<psi>'))"
      using t_not_safe_assign t_not_constraint
      unfolding f_def t_def convert_multiway.simps
      by auto
    then show ?thesis
      using And_Trigger
      unfolding f_def t_def
      by (auto simp add: fv_convert_multiway safe_formula_dual_def split: if_splits)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')

  define r where "r = Release \<phi>' I \<psi>'"
  define f where "f = And \<phi> r"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) r"
    unfolding safe_assignment_def
    by (cases r) (auto simp add: r_def)

  have t_not_constraint: "\<not>is_constraint r"
    by (auto simp add: r_def)

  have unsafe: "\<not> safe_formula (Release \<phi>' I \<psi>')"
    using And_Release
    by auto

  have "(convert_multiway f) = (convert_multiway (and_release_safe_bounded \<phi> \<phi>' I \<psi>'))"
    using t_not_safe_assign t_not_constraint unsafe And_Release(5-6)
    unfolding f_def r_def convert_multiway.simps
    by auto
  moreover have "safe_formula (convert_multiway (and_release_safe_bounded \<phi> \<phi>' I \<psi>'))"
    using And_Release.IH
    by auto

  ultimately show ?case unfolding f_def r_def by auto
next
  case (Ands l pos neg)
  define pos' where "pos' = fst (partition safe_formula (map convert_multiway l))"
  define neg' where "neg' = snd (partition safe_formula (map convert_multiway l))"

  have pos_fv: "\<Union>(set (map fv pos)) \<subseteq> \<Union>(set (map fv pos'))"
    using Ands(1,6)
    unfolding pos'_def
    by (auto simp add: list_all_iff fv_convert_multiway)

  have neg_mem: "\<forall>\<alpha> \<in> set neg'. \<exists>\<alpha>' \<in> set neg. \<alpha> = convert_multiway \<alpha>'"
  proof -
    {
      fix \<alpha>
      assume "\<alpha> \<in> set neg'"
      then have \<alpha>_props: "\<alpha> \<in> set neg'" "\<not>safe_formula \<alpha>"
        unfolding neg'_def
        by auto

      then obtain \<alpha>' where \<alpha>'_props: "\<alpha> = convert_multiway \<alpha>'" "\<alpha>' \<in> set l"
        unfolding neg'_def
        by auto
      {
        assume "safe_formula \<alpha>'"
        then have "safe_formula \<alpha>"
          using \<alpha>'_props Ands(1,6)
          by (auto simp add: list_all_iff)
        then have "False" using \<alpha>_props(2) by auto
      }
      then have "\<not>safe_formula \<alpha>'" by auto
      then have "\<alpha>' \<in> set neg" "\<alpha> = convert_multiway \<alpha>'"
        using Ands(1) \<alpha>'_props
        by auto
      then have "\<exists>\<alpha>' \<in> set neg. \<alpha> = convert_multiway \<alpha>'"
        by auto
    }
    then show ?thesis by auto
  qed

  have neg_fv: "\<Union>(set (map fv neg')) \<subseteq> \<Union>(set (map fv neg))"
  proof -
    {
      fix x
      assume "x \<in> \<Union>(set (map fv neg'))"
      then obtain \<alpha> where \<alpha>_props: "x \<in> fv \<alpha>" "\<alpha> \<in> set neg'" "\<not>safe_formula \<alpha>"
        unfolding neg'_def
        by auto

      then obtain \<alpha>' where \<alpha>'_props: "\<alpha>'\<in> set neg" "\<alpha> = convert_multiway \<alpha>'"
        using neg_mem
        by auto

      have "fv \<alpha>' = fv (convert_multiway \<alpha>')"
      proof (cases "safe_formula \<alpha>'")
        case True
        show ?thesis
          using fv_convert_multiway[OF True]
          by auto
      next
        case False
        then obtain \<alpha>'' where \<alpha>''_props: "\<alpha>' = Neg \<alpha>''" "safe_formula \<alpha>''"
          using Ands(4) \<alpha>'_props(1)
          unfolding list_all_iff
        proof -
          assume a1: "\<forall>\<phi>\<in>set neg. case \<phi> of Neg x \<Rightarrow> safe_formula x | _ \<Rightarrow> safe_formula \<phi>"
          assume a2: "\<And>\<alpha>''. \<lbrakk>\<alpha>' = Neg \<alpha>''; safe_formula \<alpha>''\<rbrakk> \<Longrightarrow> thesis"
          have "case \<alpha>' of Neg x \<Rightarrow> safe_formula x | _ \<Rightarrow> False"
            using a1 by (metis False \<open>\<alpha>' \<in> set neg\<close>)
            then show ?thesis
              using a2 case_NegE by auto
          qed
        then show ?thesis
          using fv_convert_multiway[OF \<alpha>''_props(2)]
          by auto
      qed

      
      then have "x \<in> \<Union>(set (map fv neg))"
        using \<alpha>_props(1) \<alpha>'_props(1-2)
        by (auto)
    }
    then show ?thesis by auto
  qed

  obtain \<alpha> where "\<alpha> \<in> set pos"
    using Ands(2)
    using hd_in_set
    by blast
  then have
    "\<alpha> \<in> set l"
    "safe_formula (convert_multiway \<alpha>)"
    using Ands(1,6)
    by (auto simp add: list_all_iff)
  then have "convert_multiway \<alpha> \<in> set pos'"
    unfolding pos'_def
    by auto
  then have "pos' \<noteq> []"
    by auto
  moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg'"
  proof -
    {
      fix \<phi>
      assume "\<phi> \<in> set neg'"
      then obtain \<phi>' where \<phi>'_props: "\<phi>'\<in>set neg" "\<phi> = convert_multiway \<phi>'"
        using neg_mem
        by auto
      then have \<phi>'_cases: "case \<phi>' of
           Neg \<phi>' \<Rightarrow> safe_formula (convert_multiway \<phi>')
           | _ \<Rightarrow> safe_formula \<phi>"
        "case \<phi>' of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> safe_formula \<phi>'"
        using Ands(4,7)
        by (auto simp add: list_all_iff)

      then have "(case \<phi> of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | _ \<Rightarrow> safe_formula \<phi>
        )"
        using \<phi>'_props
      proof (cases "\<phi>'")
        case (And \<alpha> \<beta>)
        then show ?thesis
          using \<phi>'_cases(1) \<phi>'_props
        proof (cases "(case \<beta> of (Release \<phi>' I \<psi>') \<Rightarrow> True | _ \<Rightarrow> False)")
          case True
          then obtain a I b where \<beta>_eq: "\<beta> = Release a I b"
            by (auto split: formula.splits)
          
          then show ?thesis
          proof (cases "safe_formula \<beta>")
            case True
            then have \<phi>_eq: "\<phi> = Ands (get_and_list (convert_multiway \<alpha>) @ get_and_list (convert_multiway (Release a I b))) "
              using \<beta>_eq And \<phi>'_cases(1) \<phi>'_props
              by (auto simp add: safe_assignment_def)
            moreover have "safe_formula \<phi>"
              using \<phi>'_cases(1) And
              by (simp)
            ultimately show ?thesis by auto
          next
            case False
            show ?thesis
            proof (cases "mem I 0")
              case mem: True
              then have \<phi>_eq: "\<phi> = And (convert_multiway \<alpha>) (convert_multiway (Release a I b))"
                using False[unfolded \<beta>_eq]
                unfolding \<phi>'_props(2) And[unfolded \<beta>_eq]
                by (auto simp add: safe_assignment_def)
              moreover have "safe_formula \<phi>"
                using \<phi>'_cases(1) And
                by (simp)
              ultimately show ?thesis by auto
            next
              case not_mem: False
              then have \<phi>_eq: "\<phi> = convert_multiway (and_release_safe_bounded \<alpha> a I b)"
                using False[unfolded \<beta>_eq]
                unfolding \<phi>'_props(2) And[unfolded \<beta>_eq]
                by (auto simp add: safe_assignment_def)
              moreover have "safe_formula \<phi>"
                using \<phi>'_cases(1) And
                by (simp)
              ultimately show ?thesis by (auto simp add: and_release_safe_bounded_def)
            qed
          qed
        qed (auto split: if_splits)
      qed (auto simp add: release_safe_0_def)
    }
    then show ?thesis by (auto simp add: list_all_iff)
  qed
  moreover have "\<Union>(set (map fv neg')) \<subseteq> \<Union>(set (map fv pos'))"
    using Ands(5) pos_fv neg_fv
    by auto
  ultimately show ?case
    unfolding neg'_def pos'_def
    by auto
next
  case (Neg \<phi>)
  have "safe_formula (Neg \<phi>') \<longleftrightarrow> safe_formula \<phi>'" if "fv \<phi>' = {}" for \<phi>'
    using that by (cases "Neg \<phi>'" rule: safe_formula.cases) simp_all
  with Neg show ?case by (simp add: fv_convert_multiway)
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  moreover {
    assume "safe_formula \<phi> \<and> safe_formula (convert_multiway \<phi>)"
    then have ?case using assms by (simp add: fv_convert_multiway safe_formula_dual_def)
  }
  (*moreover {
    assume assm: "safe_assignment (fv \<psi>) \<phi>"
    
    then have "safe_assignment (fv (convert_multiway \<psi>)) (convert_multiway \<phi>)"
      using assm assms(2-3)
      by (cases \<phi>) (auto simp add: safe_assignment_def fv_convert_multiway)

    moreover have "fv (convert_multiway \<phi>) \<subseteq> fv (convert_multiway \<psi>)"
      using assm assms(2-3)
      by (cases \<phi>) (auto simp add: safe_assignment_def fv_convert_multiway)

    ultimately have ?case
      using assms
      by (auto simp add: fv_convert_multiway)
  }
  moreover {
    assume assm: "is_constraint \<phi>"
    then have "is_constraint (convert_multiway \<phi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    moreover have "fv (convert_multiway \<phi>) \<subseteq> fv (convert_multiway \<psi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assms(2-3) assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    ultimately have ?case
      using assms
      by (auto simp add: fv_convert_multiway)
  }*)
  moreover {
    assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> safe_formula (convert_multiway \<phi>') | _ \<Rightarrow> False)"
    then obtain \<phi>' where \<phi>_def: "\<phi> = Neg \<phi>'" "safe_formula \<phi>'" "safe_formula (convert_multiway \<phi>')"
      by (auto split: formula.splits)
    then have ?case
      using assms
      by (auto simp add: fv_convert_multiway safe_formula_dual_def)
  }
  ultimately show ?case by blast
next
  case (MatchP I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
next
  case (MatchF I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
qed (auto simp add: fv_convert_multiway nfv_convert_multiway split: if_splits)

lemma future_bounded_multiway_Ands: "future_bounded (convert_multiway \<phi>) = future_bounded \<phi> \<Longrightarrow> future_bounded (Ands (get_and_list (convert_multiway \<phi>))) = future_bounded \<phi>"
  by (cases "case (convert_multiway \<phi>) of Ands l \<Rightarrow> True | _ \<Rightarrow> False") (auto split: formula.splits)

lemma release_bounded_future_bounded: "Formula.future_bounded (release_safe_bounded \<phi> I \<psi>) = (bounded I \<and> \<not>mem I 0 \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
proof (rule iffI)
  assume "Formula.future_bounded (release_safe_bounded \<phi> I \<psi>)"
  then show "bounded I \<and> \<not>mem I 0 \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>"
    by (auto simp add: release_safe_bounded_def eventually_def bounded.rep_eq flip_int_less_lower.rep_eq)
next
  assume "bounded I \<and> \<not>mem I 0 \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>"
  then show "Formula.future_bounded (release_safe_bounded \<phi> I \<psi>)"
    using flip_int_less_lower_props[of I "flip_int_less_lower I"] int_remove_lower_bound_bounded
  by (auto simp add: release_safe_bounded_def eventually_def)
qed

lemma future_bounded_convert_multiway: "safe_formula \<phi> \<Longrightarrow> future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
proof (induction \<phi> rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_safe by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?c\<psi> = list_all future_bounded (get_and_list ?c\<psi>)"
    using \<open>safe_formula \<psi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    unfolding b_def by simp
  ultimately show ?case by simp
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_Not by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    unfolding b_def by (simp add: list.pred_map o_def)
  ultimately show ?case by auto
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Trigger \<phi>' I \<psi>'"
  define f where "f = And \<phi> t"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  then show ?case proof (cases "safe_formula t")
    define l where "l = (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t))"
    case True
    then have f_convert: "convert_multiway f = Ands l"
      using t_not_safe_assign
      unfolding l_def f_def
      by auto
    have t_multiway: "future_bounded (convert_multiway t) = future_bounded t"
      using And_Trigger(6-7)
      unfolding t_def
      by auto
    have "list_all future_bounded l = (future_bounded \<phi> \<and> future_bounded (Trigger \<phi>' I \<psi>'))"
      using future_bounded_multiway_Ands[OF t_multiway] future_bounded_multiway_Ands[OF And_Trigger(5)]
      unfolding l_def t_def
      by auto
    then show ?thesis
      using f_convert
      unfolding f_def t_def
      by auto
  next
    case False
    then have convert_f: "convert_multiway f = And (convert_multiway \<phi>) (Trigger (convert_multiway \<phi>') I (convert_multiway \<psi>'))"
      using t_not_safe_assign t_not_constraint
      unfolding f_def t_def convert_multiway.simps
      by auto
    then show ?thesis
      using And_Trigger
      unfolding f_def t_def
      by (auto simp add: fv_convert_multiway safe_formula_dual_def split: if_splits)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  then show ?case using release_bounded_future_bounded
    by (auto simp add: and_release_safe_bounded_def)
next
  case (Ands l pos neg)
  then have l_future_bounded: "list_all (\<lambda>a. future_bounded (convert_multiway a) = future_bounded a) l"
  proof -
    {
      fix \<phi>
      assume assm: "\<phi> \<in> set l"
      then have "future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
      proof (cases "\<phi> \<in> set pos")
        case True
        then show ?thesis using Ands(6) by (auto simp add: list_all_iff)
      next
        case False
        then have \<phi>'_props: "case \<phi> of Neg \<phi>' \<Rightarrow> future_bounded (convert_multiway \<phi>') = future_bounded \<phi>'
           | _ \<Rightarrow> future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
          using Ands(1,7) assm
          by (auto simp add: list_all_iff)
        then show ?thesis
          by (cases \<phi>) (auto split: if_splits formula.splits)
      qed
    }
    then show ?thesis by (auto simp add: list_all_iff)
  qed
  then show ?case by (auto simp add: list_all_iff)
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  then have "future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
  proof -
    {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis by (cases \<phi>) (auto simp add: safe_assignment_def)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> future_bounded (convert_multiway \<phi>') = future_bounded \<phi>' | _ \<Rightarrow> False)"
      then have ?thesis by (cases \<phi>) (auto)
    }
    ultimately show ?thesis using assms by auto
  qed
  then show ?case using assms by auto
next
  case assms: (Release_0 \<phi> I \<psi>)
  then show ?case
    by (auto simp add: release_safe_0_def always_safe_0_def)
next
  case (MatchP I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
next
  case (MatchF I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
qed (auto simp: list.pred_set)

(* rewrite formulas *)

lemma interval_unbounded_leq:
  assumes "j \<le> i" "k \<le> j"
  assumes "\<not> bounded I" (* [a, \<infinity>] *)
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" (* if j\<le>i is part of the interval, then so is k\<le>j\<le>i *)
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  have "\<tau> \<sigma> j \<ge> \<tau> \<sigma> k" using assms by auto
  then have "\<tau> \<sigma> i - \<tau> \<sigma> j \<le> \<tau> \<sigma> i - \<tau> \<sigma> k" by linarith
  then have "memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms
    by auto
  then show ?thesis using bounded_memR assms by auto
qed

lemma interval_unbounded_geq:
  assumes "i \<le> j" "j \<le> k"
  assumes "\<not> bounded I" (* [a, \<infinity>] *)
  assumes "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" (* if j\<le>i is part of the interval, then so is k\<le>j\<le>i *)
  shows "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
proof -
  have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" using assms by auto
  then have "\<tau> \<sigma> j - \<tau> \<sigma> i \<le> \<tau> \<sigma> k - \<tau> \<sigma> i" by linarith
  then have "memL I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using assms
    by auto
  then show ?thesis using bounded_memR assms by auto
qed

lemma interval_0_bounded_geq:
  assumes "j \<le> i" "j \<le> k"
  assumes "mem I 0" "bounded I" (* [0, a] *)
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" (* if j\<le>i is part of the interval, then so is j\<le>k\<le>i *)
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" using assms by auto
  then have ineq: "\<tau> \<sigma> i - \<tau> \<sigma> j \<ge> \<tau> \<sigma> i - \<tau> \<sigma> k" by linarith
  then have "memR I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms
    by (transfer' fixing: \<sigma>) (auto split: if_splits)
  moreover have "memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using ineq assms
    by (transfer' fixing: \<sigma>) (auto split: if_splits)
  ultimately show ?thesis by auto
qed


lemma historically_rewrite_0:
  fixes I1 :: \<I>
  assumes "mem I1 0"
  shows "Formula.sat \<sigma> V v i (historically I1 \<phi>) = Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int I1"
  assume hist: "Formula.sat \<sigma> V v i (historically I1 \<phi>)"
  {
    define A where "A = {j. j\<le>i \<and> mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)}"
    define j where "j = Max A"
    assume int_bound: "bounded I1" "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using A_def by auto
    {
      fix k
      assume k_props: "j<k" "k\<le>i" 
      {
        assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        then have "False" using A_props k_props j_def A_def by auto
      }
      then have "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" by blast
      then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms I2_def
        by (transfer' fixing: \<sigma>) (auto split: if_splits)
    }
    then have "\<forall>k\<in>{j<..i}. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" by auto
    then have "\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<phi>" using hist by auto
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 Formula.TT)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>))"
      using since_true int_bound I2_def flip_int_props
      by simp
  }
  moreover {
    assume unbounded: "\<not>bounded I1"
    then have mem_leq_j: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms
      using bounded_memR memL_mono
      by blast
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using mem_leq_j hist
      by auto
  }
  moreover {
    assume "\<forall>j\<le>i. \<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then have mem_leq_j: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms I2_def
      by (transfer' fixing: \<sigma>) (auto split: if_splits)
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using mem_leq_j hist
      by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
    using I2_def historically_safe_0_def
    by auto
next
  define I2 where "I2 = flip_int I1"
  assume hist: "Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
  {
    assume int_bounded: "bounded I1"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<phi> I2 (Formula.Next all \<phi>)) (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>)))"
      using I2_def historically_safe_0_def hist
      by simp
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>)) \<or> Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))" by auto
    moreover {
      assume since: "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>))"
      then have "(\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> (\<forall>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>))" by auto
      then obtain j where j_props: "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> (\<forall>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
      {
        fix k
        assume k_props: "k\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        {
          assume "k\<le>j"
          then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j" by simp
          then have "\<tau> \<sigma> i - \<tau> \<sigma> k \<ge> \<tau> \<sigma> i - \<tau> \<sigma> j" by auto
          then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using j_props I2_def
            by (transfer' fixing: \<sigma>) (auto split: if_splits dest: memR_antimono)
          then have "False" using int_bounded k_props I2_def
            by (transfer' fixing: \<sigma>) (auto split: if_splits)
        }
        then have "\<not>(k\<le>j)" by blast
        then have "Formula.sat \<sigma> V v k \<phi>" using k_props j_props by auto
      }
      then have "Formula.sat \<sigma> V v i (historically I1 \<phi>)" by auto
    }
    moreover {
      assume "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      then have "Formula.sat \<sigma> V v i (historically I1 \<phi>)" by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (historically I1 \<phi>)" by blast
  }
  moreover {
    assume "\<not>bounded I1"
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using historically_safe_0_def hist
      by simp
    then have "Formula.sat \<sigma> V v i (historically I1 \<phi>)" by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (historically I1 \<phi>)" by blast
qed

lemma historically_rewrite_unbounded:
  assumes "\<not> mem I1 0" "\<not> bounded I1" (* [a, \<infinity>] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>)) = Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1"
  assume historically: "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>))"
  define A where "A = {j. j\<le>i \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>}"
  define j where "j = Max A"
  have "\<exists>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>" using historically by auto
  then have A_props: "finite A" "A \<noteq> {}" using A_def by auto
  then have "j \<in> A" using j_def by auto
  then have j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" using A_def by auto
  {
    fix k
    assume k_props: "k\<le>j"
    then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      using assms(2) j_props(1-2) interval_unbounded_leq[of j i k I1 \<sigma>]
      by auto
    then have first_sat: "Formula.sat \<sigma> V v k \<phi>" 
      using j_props k_props historically assms(1-2) 
      by auto
  }
  then have leq_j: "\<forall>k\<le>j. Formula.sat \<sigma> V v k \<phi>" by auto
  define B where "B = {k. k\<le>i \<and> mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)}"
  define k where "k = Min B"
  have "mem I2 0"
    using assms I2_def
    by (transfer') (auto split: if_splits)
  then have B_props: "B \<noteq> {}" "finite B" using B_def by auto
  then have k_in_B: "k \<in> B" using k_def by auto
  then have k_props: "k\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using B_def by auto
  {
    assume "k=0"
    then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
      using k_props assms flip_int_less_lower_props[of I1 I2] interval_0_bounded_geq[of k i j I2 \<sigma>] I2_def
      by auto
    then have "False"
      using assms j_props I2_def
      by (transfer') (auto split: if_splits)
  }
  then have k_pos: "k>0" by blast
  {
    assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))"
    then have "(k-1) \<in> B" using B_def k_props by auto
    then have "(k-1) \<ge> k" using B_props k_def by auto
    then have "False" using k_pos by auto
  }
  then have "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))" by blast
  then have k_pre: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))"
    using assms flip_int_less_lower_mem I2_def
    by auto
  then have "Formula.sat \<sigma> V v (k-1) \<phi>" using historically k_props by auto
  then have "(k-1) \<in> A" using A_def k_pre k_props by auto
  then have "(k-1) \<le> j" using j_def A_props by auto
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))))"
    using interval_all k_pos leq_j k_props
    by (auto split: nat.split)
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) \<and> Formula.sat \<sigma> V v i (once I1 \<phi>)"
    using historically
    by auto
  then show "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
    using assms historically_safe_unbounded_def I2_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1"
  define A where "A = {j. j\<le>i \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)}"
  assume "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) (once I1 \<phi>))"
    using assms historically_safe_unbounded_def I2_def
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.And (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) (once I1 \<phi>))"
    by auto
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))))" by auto
  then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))"
    by auto
  then obtain j where j_props:
    "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))"
    by blast
  {
    assume "j = 0"
    then have "\<not>Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))" by auto
    then have "False" using j_props by auto
  }
  then have j_pos: "j \<noteq> 0" by auto
  then have j_pred_sat: "Formula.sat \<sigma> V v (j-1) (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))"
    using j_pos j_props
    by (simp add: Nitpick.case_nat_unfold)
  {
    fix x
    assume x_props: "x>j-1"
    then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" using x_props by auto
    then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      using j_props assms flip_int_less_lower_props[of I1 I2] interval_0_bounded_geq[of j i x I2] I2_def
      by auto
    then have "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      using assms I2_def
      by (transfer') (auto split: if_splits)
  }
  then have x_greater: "\<forall>x>(j-1). \<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by blast
  {
    fix x
    assume x_props: "x\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
    {
      assume "x>(j-1)"
      then have "False" using x_props x_greater by auto
    }
    then have "\<not>(x>j-1)" by blast
    then have "x\<le>(j-1)" by auto
  }
  then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> x\<le>j-1" by blast
  then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<phi>" using j_pred_sat by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>))" using rewrite by auto
qed

lemma historically_rewrite_bounded:
  fixes I1 :: \<I>
  assumes "\<not>mem I1 0" "bounded I1" (* [a, b], a>0 *)
  (*
    [0, b-a] would be more efficient but this interval can
    (probably) not be constructed using the current
    implementation of intervals.
  *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>)) = Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
proof (rule iffI)
  assume "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>))"
  then show "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
    using assms historically_safe_bounded_def
    by auto
next
  define I2 where "I2 = int_remove_lower_bound I1"
  assume "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Neg (once I1 (Formula.And (Formula.Or (once I2 \<phi>) (eventually I2 \<phi>)) (Formula.Neg \<phi>)))))"
    using assms I2_def historically_safe_bounded_def
    by auto
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" by auto
  have j_leq_i_sat: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> (Formula.sat \<sigma> V v j (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v j (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    then have "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v k \<phi>"
      using j_leq_i_sat by auto
    moreover {
      assume assm: "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" by auto
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
          using j_props assms(1-2)
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
          using k_props assms(1-2)
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (metis diff_le_mono int_remove_lower_bound.rep_eq le_eq_less_or_eq memR.rep_eq memR_antimono neq0_conv prod.sel(1) prod.sel(2) zero_less_diff)
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms I2_def
          by (metis diff_le_mono int_remove_lower_bound.rep_eq le_eq_less_or_eq memR.rep_eq memR_antimono neq0_conv prod.sel(1) prod.sel(2) zero_less_diff)
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "Formula.sat \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j \<phi>" by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>))" using rewrite by auto
qed

lemma sat_trigger_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
  assumes leq: "j\<le>i"
  assumes mem_j: "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
  shows "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {j<..i}. Formula.sat \<sigma> V v x \<phi>}"
  define k where "k = Max A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {j<..i}" "Formula.sat \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "\<forall>l>k. l \<notin> A"
    using Max_ge[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    using mem mem_j k_props interval_geq[of I 0 \<sigma> i j k]
    by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat_trigger_rewrite_0:
  assumes "mem I 0"
shows "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>) = Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
  {
    assume "\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>))"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by auto
  }
  moreover {
    define A where "A = {j. j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)}"
    define j where "j = Max A"
    assume "\<not>(\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then obtain j' where j'_props: "j' \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j')" "\<not>Formula.sat \<sigma> V v j' (Formula.And \<psi> (Formula.Neg \<phi>))" by blast
    then have "\<not>Formula.sat \<sigma> V v j' \<psi> \<or> Formula.sat \<sigma> V v j' \<phi>" by simp
    moreover {
      assume "\<not>Formula.sat \<sigma> V v j' \<psi>"
      then have "\<exists>k \<in> {j'<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)"
      using j'_props assms trigger sat_trigger_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {j<..i} \<and> \<not> Formula.sat \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        using assms j_props interval_geq[of I 0 \<sigma> i j k]
        by auto
      then have "\<exists>x \<in> {k<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> x) \<and> Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        using assms trigger k_props sat_trigger_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {k<..i}" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> x)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        by blast
      then have "x \<le> Max A"
        using A_def A_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<psi>" by blast
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I (Formula.And \<psi> (Formula.Neg \<phi>))))"
      using j_props
      by auto
    }
    moreover {
      define B where "B = {j. j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>}"
      define k where "k = Max B"
      assume "Formula.sat \<sigma> V v j' \<phi>"
      then have B_props: "B \<noteq> {}" "finite B" using B_def j'_props by auto
      then have "k \<in> B" using k_def by auto
      then have k_props: "k\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)" "Formula.sat \<sigma> V v k \<phi>" using B_def by auto
      have "\<forall>l>k. l \<notin> B"
        using Max_ge[OF B_props(2)]
        by (fastforce simp: k_def)
      {
        fix l
        assume l_props: "l \<in> {k<..i}"
        then have l_mem: "mem I (\<tau> \<sigma> i - \<tau> \<sigma> l)"
          using assms k_props interval_geq[of I 0 \<sigma> i k l]
          by auto
        {
          assume "Formula.sat \<sigma> V v l \<phi>"
          then have "l \<in> B" using B_def l_props l_mem by auto
          then have "l\<le>k" "l>k"
            using k_def l_props B_props(2) Max_ge[of B l]
            by auto
        }
        then have "\<not>Formula.sat \<sigma> V v l \<phi>" by auto
      }
      then have not_phi: "\<forall>l\<in>{k<..i}. \<not>Formula.sat \<sigma> V v l \<phi>" using assms B_def by auto
      
      then have k_sat_psi: "Formula.sat \<sigma> V v k \<psi>" using k_props trigger B_def by auto
      {
        fix l
        assume l_props: "l\<in>{k<..i}"
        then have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> l)"
          using k_props assms interval_geq[of I 0 \<sigma> i k l]
          by auto
        then have "Formula.sat \<sigma> V v l \<psi>"
          using l_props trigger not_phi
          by auto
      }
      then have "\<forall>l\<in>{k<..i}. Formula.sat \<sigma> V v l \<psi>"
        using not_phi assms trigger
        by auto
      then have "Formula.sat \<sigma> V v i (Formula.Since \<psi> I (Formula.And \<phi> \<psi>))"
        using k_props k_sat_psi
        by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by blast
  then show "Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
    using assms historically_rewrite_0[of I \<sigma> V v i "\<psi>"] trigger_safe_0_def
    by auto
next
  assume "Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I \<psi>))"
    using trigger_safe_0_def assms historically_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (historically I (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
      by auto
  }
  moreover {
    fix j
    assume since_and_j_props: "Formula.sat \<sigma> V v i (Formula.Since \<psi> I (Formula.And \<phi> \<psi>))" "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then obtain "j'" where j'_props:
      "j'\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j')" "Formula.sat \<sigma> V v j' (Formula.And \<phi> \<psi>)"
      "(\<forall>k \<in> {j' <.. i}. Formula.sat \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume le: "j' < j"
      then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
        using j'_props since_and_j_props le
        by auto
    }
    moreover {
      assume geq: "\<not> j' < j"
      moreover {
        assume "j = j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
          using geq j'_props
          by auto
      }
      ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)" by auto
qed

lemma sat_trigger_rewrite:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" (* [a, b] *)
  assumes "I2 = flip_int_less_lower I1" (* [0, a-1] *)
shows "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>) = Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
proof (rule iffI)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)"
  {
    assume "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> all (Formula.And \<phi> \<psi>)))))" by auto
  }
  moreover {
    assume "\<exists>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> \<not>Formula.sat \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "\<not>Formula.sat \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{j <.. i} \<and> Formula.sat \<sigma> V v k \<phi>}"
    define k where k_def: "k = Max A"
    have "(\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" using j_props trigger by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{j <.. i}" "Formula.sat \<sigma> V v k \<phi>" using A_def by auto
    {
      fix x
      assume x_props: "x\<ge>j" "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      {
        assume k_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
        have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" using x_props by auto
        then have "\<tau> \<sigma> i - \<tau> \<sigma> x \<le> \<tau> \<sigma> i - \<tau> \<sigma> j" by auto
        moreover have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms j_props by auto 
        ultimately have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using memR_antimono by blast
        moreover have "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
          using x_props assms
          by (metis flip_int_less_lower.rep_eq memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
        ultimately have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using assms by auto
        then have "False" using k_not_mem_1 by auto
      }
      then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by auto
    }
    then have geq_j_mem: "\<forall>x\<ge>j. \<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by auto
    {
      assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      then have k_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using geq_j_mem k_props by auto
      then have "Formula.sat \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {k <.. i}. Formula.sat \<sigma> V v k \<phi>)" using trigger k_props by auto
      moreover {
        assume "(\<exists>k \<in> {k <.. i}. Formula.sat \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {k <.. i}" "Formula.sat \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "Formula.sat \<sigma> V v k \<psi>" by auto
      then have k_sat: "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_props by auto
      then have k_since: "Formula.sat \<sigma> V v k (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
        using int_remove_lower_bound.rep_eq memL.rep_eq by auto
      {
        assume "k=i"
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] assms k_mem
          by auto
      }
      moreover {
        assume "\<not>(k=i)"
        then have k_suc_leq_i: "k+1\<le>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {k<..i}" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
          then have "Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>)" using trigger by auto
          moreover {
            assume "\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {x <.. i}" "Formula.sat \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<le> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{k<..i}. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))"
          moreover have "Formula.sat \<sigma> V v (k+1) (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
            using k_suc_leq_i k_since interval_all
            by auto
          ultimately have "(\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            using k_suc_leq_i
            by blast
          then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{k<..i} \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l) \<and> Formula.sat \<sigma> V v l \<psi>}"
          define c where "c = Max B"
          assume "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))" using geq_j_mem k_props by auto
          then have "Formula.sat \<sigma> V v (k+1) \<psi> \<or> (\<exists>x \<in> {k+1 <.. i}. Formula.sat \<sigma> V v x \<phi>)" using trigger k_suc_leq_i by auto
          moreover {
            assume "\<exists>x \<in> {k+1 <.. i}. Formula.sat \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {k+1 <.. i} \<and> Formula.sat \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<le> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v (k+1) \<psi>" by auto
          then have B_props: "B \<noteq> {}" "finite B" using B_def k_suc_leq_i k_suc_mem k_props by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{k<..i}" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> c)" "Formula.sat \<sigma> V v c \<psi>"
            using B_def
            by auto
          then have k_cond: "k\<le>c" "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_sat by auto
          {
            fix x
            assume x_props: "x\<in>{k<..c}"
            then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> c" by auto
            then have lower: "(\<tau> \<sigma> i - \<tau> \<sigma> x) \<ge> (\<tau> \<sigma> i - \<tau> \<sigma> c)" by linarith
            have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> k" using x_props by auto
            then have upper: "(\<tau> \<sigma> i - \<tau> \<sigma> x) \<le> (\<tau> \<sigma> i - \<tau> \<sigma> k)" by linarith
            then have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
              using k_mem memR_antimono by blast
            then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using assms c_props lower by auto
            then have "Formula.sat \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{k<..c}. Formula.sat \<sigma> V v x \<psi>" by auto
          moreover have "mem (int_remove_lower_bound I1) (\<tau> \<sigma> c - \<tau> \<sigma> k)"
            using k_mem c_props
          by (metis diff_is_0_eq diff_self_eq_0 greaterThanAtMost_iff int_remove_lower_bound.rep_eq interval_leq memL.rep_eq memR.rep_eq prod.sel(1-2))
          ultimately have c_sat: "Formula.sat \<sigma> V v c (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
            using k_cond
            by auto
          {
            assume "(c+1) \<in> B"
            then have "c+1\<le>c" using c_def B_props by auto
            then have "False" by auto
          }
          then have "(c+1) \<notin> B" by blast
          then have disj: "(c+1)\<notin>{k<..i} \<or> \<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1)) \<or> \<not>Formula.sat \<sigma> V v (c+1) \<psi>" using B_def by blast
          {
            assume "(c+1)\<notin>{k<..i}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c+1)\<notin>{k<..i})"
            then have c_suc_leq_i: "(c+1)\<in>{k<..i}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1)) \<or> \<not>Formula.sat \<sigma> V v (c+1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
              then have "\<not>Formula.sat \<sigma> V v (c+1) \<psi>" using disj by blast
              then have "False"
                using k_greater_sat c_suc_leq_i c_suc_mem
                by auto
            }
            moreover {
              assume c_suc_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
              {
                assume not_mem2: "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                then have upper: "\<not>memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                  using c_suc_not_mem_1 assms geq_j_mem k_cond k_props
                  by auto
                have "\<tau> \<sigma> c \<le> \<tau> \<sigma> (c+1)" by auto
                then have "\<tau> \<sigma> i - \<tau> \<sigma> c \<ge> \<tau> \<sigma> i - \<tau> \<sigma> (c+1)" using diff_le_mono2 by blast
                moreover have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> c)" using c_props assms by auto
                ultimately have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                  using not_mem2 memR_antimono
                  by blast
                then have "False" using upper by auto
              }
              then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))" by blast
              then have "(c+1)\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))" "Formula.sat \<sigma> V v (c+1) (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
                using c_suc_leq_i c_sat interval_all
                by auto
              then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
                using interval_all sat_once
                by blast
            }
            ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by auto
          }
          ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by blast
        }
        ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
          by blast
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by auto
next
  assume "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
  then have "Formula.sat \<sigma> V v i (historically I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (historically I1 \<psi>)"
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (once I2 \<phi>)"
    then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" by blast
    {
      fix x
      assume x_props: "x\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      {
        assume j_leq_x: "x\<ge>j"
        then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using j_leq_x j_props assms
          using flip_int_less_lower_props interval_0_bounded_geq memR_zero
          by blast
        then have "False"
          using x_props assms flip_int_less_lower.rep_eq memR.rep_eq memR_zero
          by auto
      }
      then have "\<not>(x\<ge>j)" by blast
      then have "x<j" by auto
    }
    then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> x<j" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume since: "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by blast
    {
      assume "j = 0"
      then have "\<not>Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
      then have "False" using j_props by auto
    }
    then have j_pos: "j>0" by auto
    then have j_pred_sat: "Formula.sat \<sigma> V v (j-1) (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
      using j_pos j_props
      by (simp add: Nitpick.case_nat_unfold)
    then have "\<exists>x\<le>(j-1). Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>) \<and> (\<forall>k\<in>{x<..(j-1)}. Formula.sat \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<le>(j-1)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)" "\<forall>k\<in>{x<..(j-1)}. Formula.sat \<sigma> V v k \<psi>"
      by blast
    {
      fix l
      assume l_props: "l\<le>i"
      {
        assume "l<x"
        then have "\<exists>k \<in> {l <.. i}. Formula.sat \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l<x)" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
        then have l_props: "x\<le>l" "l\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)" using l_props by auto
        {
          assume "l\<le>(j-1)"
          then have "Formula.sat \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<le>(j-1)"
          then have l_geq: "l\<ge>(j-1)" by auto
          have j_pred_psi: "Formula.sat \<sigma> V v (j-1) \<psi>" using j_pred_sat by auto
          {
            assume l_greater: "l>(j-1)"
            then have "\<tau> \<sigma> l \<ge> \<tau> \<sigma> j" by auto
            then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
              using assms j_props j_pos l_greater flip_int_less_lower_props interval_0_bounded_geq
              by (metis One_nat_def Suc_pred le_simps(3) memR_zero)
            then have "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
              using assms flip_int_less_lower.rep_eq memR.rep_eq memR_zero
              by auto
            then have "False" using l_assms by auto
          }
          then have "l=(j-1)" using l_geq le_eq_less_or_eq by blast
          then have "Formula.sat \<sigma> V v l \<psi>" using j_pred_psi by blast
        }
        ultimately have "Formula.sat \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l) \<longrightarrow> Formula.sat \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {l <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by blast
qed

lemma sat_trigger_rewrite_unbounded:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" "\<not>bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
  have disj: "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using trigger assms I2_def sat_trigger_rewrite
      by auto
  {
    assume "Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (once I1 \<psi>)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      using disj assms historically_rewrite_unbounded[of I1 \<sigma> V v i \<psi>]
    by simp
  }
  moreover {
    assume "\<not>Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (once I2 \<phi>) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using disj j_props
      by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      by simp
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_unbounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using trigger
    by auto
  then show "Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
    using trigger_safe_unbounded_def[of \<phi> I1 \<psi>] assms I2_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_unbounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def trigger_safe_unbounded_def
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
    using assms historically_rewrite_unbounded[of I1 \<sigma> V v i \<psi>]
    by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
    using assms I2_def sat_trigger_rewrite assm
    by auto
qed

lemma sat_trigger_rewrite_bounded:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" "bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
  have disj: "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using trigger assms I2_def sat_trigger_rewrite
      by auto
  {
    assume "Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (once I1 \<psi>)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      using disj assms historically_rewrite_bounded[of I1 \<sigma> V v i \<psi>]
    by simp
  }
  moreover {
    assume "\<not>Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (once I2 \<phi>) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using disj j_props
      by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      by simp
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_bounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using trigger
    by auto
  then show "Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
    using trigger_safe_bounded_def[of \<phi> I1 \<psi>] assms I2_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_bounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def trigger_safe_bounded_def
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
    using assms historically_rewrite_bounded[of I1 \<sigma> V v i]
    by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
    using assms I2_def sat_trigger_rewrite assm
    by auto
qed

lemma sat_and_trigger_bounded_rewrite:
  assumes "bounded I" "\<not>mem I 0" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) = Formula.sat \<sigma> V v i (and_trigger_safe_bounded \<phi> \<phi>' I \<psi>')"
proof (cases "\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)")
  case True
  then have once: "sat \<sigma> V v i (once I TT)"
    by auto
  then have "sat \<sigma> V v i (Trigger \<phi>' I \<psi>') = sat \<sigma> V v i (trigger_safe_bounded \<phi>' I \<psi>')"
    using sat_trigger_rewrite_bounded[OF assms(2,1), of \<sigma> V v i]
    by auto
  moreover have "
    sat \<sigma> V v i (Or (And \<phi> (Neg (once I TT))) (And \<phi> (trigger_safe_bounded \<phi>' I \<psi>'))) =
    sat \<sigma> V v i (And \<phi> (trigger_safe_bounded \<phi>' I \<psi>'))"
    using once
    by auto
  ultimately show ?thesis
    unfolding and_trigger_safe_bounded_def
    by auto
qed (auto simp add: and_trigger_safe_bounded_def)

lemma sat_and_trigger_unbounded_rewrite:
  assumes "\<not>bounded I" "\<not>mem I 0" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) = Formula.sat \<sigma> V v i (and_trigger_safe_unbounded \<phi> \<phi>' I \<psi>')"
proof (cases "\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)")
  case True
  then have once: "sat \<sigma> V v i (once I TT)"
    by auto
  then have "sat \<sigma> V v i (Trigger \<phi>' I \<psi>') = sat \<sigma> V v i (trigger_safe_unbounded \<phi>' I \<psi>')"
    using sat_trigger_rewrite_unbounded[OF assms(2,1), of \<sigma> V v i]
    by auto
  moreover have "
    sat \<sigma> V v i (Or (And \<phi> (Neg (once I TT))) (And \<phi> (trigger_safe_unbounded \<phi>' I \<psi>'))) =
    sat \<sigma> V v i (And \<phi> (trigger_safe_unbounded \<phi>' I \<psi>'))"
    using once
    by auto
  ultimately show ?thesis
    unfolding and_trigger_safe_unbounded_def
    by auto
qed (auto simp add: and_trigger_safe_unbounded_def)

lemma always_rewrite_0:
  fixes I :: \<I>
  assumes "mem I 0" "bounded I"
  shows "Formula.sat \<sigma> V v i (always I \<phi>) = Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)"
proof (rule iffI)
  assume all: "Formula.sat \<sigma> V v i (always I \<phi>)"
  {
    define A where "A = {j. j\<ge>i \<and> mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)}"
    define j where "j = Inf A"
    assume "\<exists>j\<ge>i. mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then have "A \<noteq> {}" using A_def by auto
    then have "j \<in> A" using j_def by (simp add: Inf_nat_def1)
    then have j_props: "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" using A_def by auto
    {
      fix k
      assume k_props: "k \<in> {i..<j}"
      then have ineq: "\<tau> \<sigma> k - \<tau> \<sigma> i \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" by (simp add: diff_le_mono)
      {
        assume "mem (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        then have "k \<in> A" using A_def k_props by auto
        then have "k \<ge> j" using j_def cInf_lower by auto
        then have "False" using k_props by auto
      }
      then have "\<not>mem (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using j_props ineq assms(1) flip_int_double_upper_leq[of I "(\<tau> \<sigma> j - \<tau> \<sigma> i)" "(\<tau> \<sigma> k - \<tau> \<sigma> i)"]
        by auto 
      then have "Formula.sat \<sigma> V v k \<phi>" using k_props all by auto
    }
    then have until_j: "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>" by blast
    have "\<not> mem (flip_int_double_upper I) 0"
      using assms
      by (simp add: flip_int_double_upper.rep_eq memL.rep_eq)
    then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>))"
      using j_props until_j until_true[of "(flip_int_double_upper I)" \<sigma> V v i \<phi>]
      by auto
  }
  moreover {
    define B where "B = {b. \<not>memR I b}"
    define b where "b = Inf B"
    define C where "C = {k. k\<ge>i \<and> b \<le> \<tau> \<sigma> k - \<tau> \<sigma> i}"
    define c where "c = Inf C"
    assume empty_int: "\<forall>j\<ge>i. \<not> mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" (* [b+1, 2b] *)
    from assms(2) have "B \<noteq> {}" using B_def bounded_memR by auto
    then have "b \<in> B" using b_def by (simp add: Inf_nat_def1)
    then have b_props: "\<not>memR I b" using B_def by auto
   
    have exists_db: "\<And>x. \<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i"
    proof -
      fix x
      show "\<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i"
        using ex_le_\<tau>[of i "x + \<tau> \<sigma> i" \<sigma>]
        by auto
    qed
    then have "C \<noteq> {}" using C_def by auto
    then have "c \<in> C" using c_def by (simp add: Inf_nat_def1)
    then have c_props: "c\<ge>i" "b \<le> \<tau> \<sigma> c - \<tau> \<sigma> i" using C_def by auto
    {
      assume "b = 0"
      then have "False" using b_props by auto
    }
    then have b_pos: "b>0" by blast
    {
      assume "c = i"
      then have "False" using c_props b_pos by auto
    }
    then have c_ge_i: "c>i" using c_props using le_less by blast
    {
      assume "\<not>mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
      then have "\<not>memR I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" using assms(1) memL_mono by blast
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<in> B" using B_def by auto
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<ge> b" using b_def cInf_lower by auto
      then have "(c-1) \<in> C" using C_def c_ge_i by auto
      then have "c-1 \<ge> c" using c_def cInf_lower by auto
      then have "False" using c_ge_i by auto
    }
    then have c_pred_mem: "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by blast
    then have c_pred_sat: "Formula.sat \<sigma> V v (c-1) \<phi>" using all c_ge_i by auto
    {
      assume "\<not>mem (flip_int I) (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" (* [b+1, \<infinity>] but attention, here 'b' = b+1 *)
      then have "memR I (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" using assms(1) bounded_memR int_flip_mem by blast
      then have c_dist: "(\<tau> \<sigma> c - \<tau> \<sigma> (c-1)) < b" using b_props memR_antimono not_le by blast
      from c_pred_mem have "memR I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by auto
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) < b" using b_props memR_antimono not_le by blast
      then have b_ineq: "b \<le> (\<tau> \<sigma> c - \<tau> \<sigma> i)" "(\<tau> \<sigma> c - \<tau> \<sigma> i) \<le> 2 * (b-1)"
        using c_props c_dist
        by auto
      {
        assume "\<not>memR I (b-1)"
        then have "(b-1) \<in> B" using B_def by auto
        then have "(b-1) \<ge> b" using b_def cInf_lower by auto
        then have "False" using b_pos by linarith
      }
      then have "memR I (b-1)" by blast
      then have "(\<lambda>i. memR I ((div) i 2)) (2*(b-1))" by auto
      then have "(\<lambda>i. memR I ((div) i 2)) (\<tau> \<sigma> c - \<tau> \<sigma> i)" using b_ineq by auto
      then have "memR (flip_int_double_upper I) (\<tau> \<sigma> c - \<tau> \<sigma> i)"
        by (simp add: flip_int_double_upper.rep_eq memR.rep_eq)
      moreover have "memL (flip_int_double_upper I) (\<tau> \<sigma> c - \<tau> \<sigma> i)"
        using b_ineq b_props flip_int_double_upper.rep_eq memL.rep_eq memR_antimono
        by auto
      ultimately have "False" using empty_int c_props by auto
    }
    then have "mem (flip_int I) (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" by blast
    then have c_pred_sat: "Formula.sat \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      using c_pred_sat c_ge_i
      by auto
    have "\<forall>j\<in>{i..<(c-1)}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
      by (meson \<tau>_mono assms(1) atLeastLessThan_iff c_pred_mem diff_le_mono le_eq_less_or_eq memL_mono memR_antimono zero_le)
    then have "\<forall>j\<in>{i..<(c-1)}. Formula.sat \<sigma> V v j \<phi>" using all by auto
    then have
        "(c-1)\<ge>i"
        "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
        "Formula.sat \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
        "(\<forall>k \<in> {i ..< (c-1)}. Formula.sat \<sigma> V v k \<phi>)"
      using c_ge_i c_pred_mem c_pred_sat
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
      by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    by auto
  then show "Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)" using always_safe_0_def by auto
next
  assume "Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    using always_safe_0_def
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT) \<or> Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))" by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT)"
    then obtain j where j_props:
      "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>"
      by auto
    then have "\<forall>k\<ge>i. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<longrightarrow> k<j"
      by (metis (no_types, lifting) assms flip_int_double_upper.rep_eq forall_finite(1) interval_leq leI memL.rep_eq prod.sel(1))
    then have "Formula.sat \<sigma> V v i (always I \<phi>)" using j_props by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
    then obtain j where j_props:
      "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>"
      by auto
    then have phi_sat: "\<forall>k\<in>{i..j}. Formula.sat \<sigma> V v k \<phi>" by auto
    {
      fix k
      assume k_props: "k>j" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have t_geq: "(\<tau> \<sigma> k - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)" using diff_le_mono by auto
      from j_props have "mem (flip_int I) (\<tau> \<sigma> (j+1) - \<tau> \<sigma> j)" by auto
      then have "\<not>mem I (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)"
        by (metis \<tau>_mono assms(2) diff_le_mono2 flip_int.rep_eq j_props(1) memL.rep_eq memL_mono prod.sel(1))
      then have "\<not>memR I (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)" using assms memL_mono by blast
      then have "\<not>memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using t_geq memR_antimono by blast
      then have "False" using k_props by auto
    }
    then have "\<forall>k>j. \<not>mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
    then have "Formula.sat \<sigma> V v i (always I \<phi>)" using phi_sat by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (always I \<phi>)" by blast
qed

lemma always_rewrite_bounded:
  fixes I1 :: \<I>
  assumes "bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>)) = Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
proof (rule iffI)
  assume "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>))"
  then show "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
    using assms always_safe_bounded_def
    by auto
next
  define I2 where "I2 = int_remove_lower_bound I1"
  assume "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (Formula.Neg (eventually I1 (Formula.And (Formula.Or (once I2 \<phi>) (eventually I2 \<phi>)) (Formula.Neg \<phi>)))))"
    using assms I2_def always_safe_bounded_def
    by auto
  then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j \<phi>" by auto
  have j_geq_i_sat: "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> (Formula.sat \<sigma> V v j (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v j (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<ge>i" "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
    then have "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v k \<phi>"
      using j_geq_i_sat by auto
    moreover {
      assume assm: "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" by auto
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          using j_props assms
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
          using k_props assms
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def interval_geq j_props(1)
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms I2_def j_props(1) k_props(1) interval_geq
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "Formula.sat \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<phi>" by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>))"
    using rewrite
    by auto
qed

lemma sat_release_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  assumes geq: "j\<ge>i"
  assumes mem_j: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  shows "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {i..<j}. Formula.sat \<sigma> V v x \<phi>}"
  define k where "k = Min A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {i..<j}" "Formula.sat \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "(\<forall>l<k. l \<notin> A)"
    using Min_le[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using mem mem_j k_props interval_leq[of I 0 \<sigma> j i k] by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat_release_rewrite_0:
  assumes mem: "mem I 0" "bounded I"
shows "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume release: "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  {
    assume "\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>))"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  moreover {
    assume "\<not>(\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then obtain j' where j'_props: "j' \<ge> i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "\<not>Formula.sat \<sigma> V v j' (Formula.And \<psi> (Formula.Neg \<phi>))" by blast
    define A where "A = {j. j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)}"
    define j where "j = Min A"
    from j'_props have "\<not>Formula.sat \<sigma> V v j' \<psi> \<or> Formula.sat \<sigma> V v j' \<phi>" by simp
    moreover {
      assume "\<not>Formula.sat \<sigma> V v j' \<psi>"
      then have "\<exists>k \<in> {i..<j'}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)"
      using j'_props assms release sat_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {i..<j} \<and> \<not> Formula.sat \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using assms j_props interval_leq[of I 0 \<sigma> j i k]
        by auto
      then have "\<exists>x \<in> {i..<k}. mem I (\<tau> \<sigma> x - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        using assms release k_props sat_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {i..<k}" "mem I (\<tau> \<sigma> x - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        by blast
      then have "x \<ge> Min A"
        using A_def A_props k_props j_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<psi>" by blast
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))"
      using j_props
      by auto
    }
    moreover {
      define B where "B = {j. j\<in>{i..j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j \<phi>}"
      define k where "k = Min B"
      assume "Formula.sat \<sigma> V v j' \<phi>"
      then have B_props: "B \<noteq> {}" "finite B" using B_def j'_props by auto
      then have "k \<in> B" using k_def by auto
      then have k_props: "k\<in>{i..j'}" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v k \<phi>" using B_def by auto
      have "\<forall>l<k. l \<notin> B"
        using Min_le[OF B_props(2)]
        by (fastforce simp: k_def)
      {
        fix l
        assume l_props: "l \<in> {i..<k}"
        then have l_mem: "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using assms k_props interval_leq[of I 0 \<sigma> k i l]
          by auto
        {
          assume "Formula.sat \<sigma> V v l \<phi>"
          then have "l \<in> B" using B_def l_props l_mem k_props by auto
          then have "l\<ge>k" "l<k"
            using k_def l_props B_props(2) Min_le[of B l]
            by auto
        }
        then have "\<not>Formula.sat \<sigma> V v l \<phi>" by auto
      }
      then have not_phi: "\<forall>l\<in>{i..<k}. \<not>Formula.sat \<sigma> V v l \<phi>" using assms B_def by auto
      
      then have k_sat_psi: "Formula.sat \<sigma> V v k \<psi>" using k_props release B_def by auto
      {
        fix l
        assume l_props: "l\<in>{i..<k}"
        then have "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using k_props assms interval_leq[of I 0 \<sigma> k i l]
          by auto
        then have "Formula.sat \<sigma> V v l \<psi>"
          using l_props release not_phi
          by auto
      }
      then have "\<forall>l\<in>{i..<k}. Formula.sat \<sigma> V v l \<psi>"
        using not_phi assms release
        by auto
      then have "Formula.sat \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))"
        using k_props k_sat_psi
        by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by blast
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I \<psi>))"
    using assms always_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  then show "Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
next
  assume "Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I \<psi>))"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))"
    using assms always_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (always I \<psi>)"
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
  }
  moreover {
    fix j
    assume until_and_j_props: "Formula.sat \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))" "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then obtain "j'" where j'_props: "j'\<ge>i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j' (Formula.And \<phi> \<psi>)" "(\<forall>k \<in> {i ..< j'}. Formula.sat \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume ge: "j' > j"
      then have "\<forall>k \<in> {i ..< j'}. Formula.sat \<sigma> V v k \<psi>" using j'_props by auto
      then have "Formula.sat \<sigma> V v j \<psi>" using until_and_j_props ge by auto
      then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by auto
    }
    moreover {
      assume leq: "\<not> j' > j"
      moreover {
        assume "j = j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using leq j'_props
          by auto
      }
      ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
qed

lemma sat_release_rewrite:
  fixes I1 I2 :: \<I>
  assumes "bounded I1" "\<not>mem I1 0" (* [a, b] *)
shows "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume release: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
  {
    assume "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<psi>"
    then have all: "Formula.sat \<sigma> V v i (always I1 \<psi>)" by auto
    obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using release by auto
    then have "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>)"
      using assms always_rewrite_bounded[of I1 \<sigma> V v i \<psi>] all
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      by auto
  }
  moreover {
    assume "\<exists>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> \<not>Formula.sat \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<not>Formula.sat \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{i ..< j} \<and> Formula.sat \<sigma> V v k \<phi>}"
    define k where k_def: "k = Min A"
    have "(\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" using j_props release by auto
    then have A_props: "A \<noteq> {}" "finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{i ..< j}" "Formula.sat \<sigma> V v k \<phi>" using A_def by auto
    {
      fix x
      assume x_props: "x\<le>j" "\<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume k_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
        have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" using x_props by auto
        then have "\<tau> \<sigma> x - \<tau> \<sigma> i \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" by linarith
        moreover have "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using assms j_props by auto 
        ultimately have "memR I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using memR_antimono by blast
        moreover have "memL I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          using k_not_mem_1 x_props assms I2_def
          by (metis flip_int_less_lower.rep_eq memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
        ultimately have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms by auto
        then have "False" using k_not_mem_1 by auto
      }
      then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    }
    then have geq_j_mem: "\<forall>x\<le>j. \<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    {
      assume "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have k_mem: "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
      then have "Formula.sat \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {i ..< k}. Formula.sat \<sigma> V v k \<phi>)" using release k_props by auto
      moreover {
        assume "(\<exists>k \<in> {i ..< k}. Formula.sat \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {i ..< k}" "Formula.sat \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "Formula.sat \<sigma> V v k \<psi>" by auto
      then have k_sat: "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_props by auto
      then have k_until: "Formula.sat \<sigma> V v k (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
        using assms int_remove_lower_bound.rep_eq memL.rep_eq prod.sel(1)
        by auto
      {
        assume "k=i"
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] using assms k_mem by auto
      }
      moreover {
        assume k_neq_i: "\<not>(k=i)"
        then have k_pred_geq_i: "k-1\<ge>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {i..<k}" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          then have "Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>)" using release by auto
          moreover {
            assume "\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {i ..< x}" "Formula.sat \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<ge> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{i..<k}. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          moreover have "Formula.sat \<sigma> V v (k-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
            using k_pred_geq_i k_until interval_all k_neq_i
            by auto
          ultimately have "(\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            using k_pred_geq_i
            by blast
          then have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{i..<k} \<and> mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v l \<psi>}"
          define c where "c = Min B"
          assume "\<not>mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
          then have "Formula.sat \<sigma> V v (k-1) \<psi> \<or> (\<exists>x \<in> {i ..< k-1}. Formula.sat \<sigma> V v x \<phi>)"
            using release k_pred_geq_i
            by auto
          moreover {
            assume "\<exists>x \<in> {i ..< k-1}. Formula.sat \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {i ..< k-1} \<and> Formula.sat \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<ge> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v (k-1) \<psi>" by auto
          then have B_props: "B \<noteq> {} \<and> finite B"
            using B_def k_pred_geq_i k_suc_mem k_props k_neq_i
            by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{i..<k}" "mem I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v c \<psi>" using B_def by auto
          then have k_cond: "k\<ge>c" "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_sat by auto
          {
            assume "c=0"
            then have "False" using c_props assms by auto
          }
          then have c_pos: "c\<noteq>0" by auto
          {
            fix x
            assume x_props: "x\<in>{c..<k}"
            then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> c" by auto
            then have lower: "(\<tau> \<sigma> x - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> c - \<tau> \<sigma> i)" by auto
            have "\<tau> \<sigma> x \<le> \<tau> \<sigma> k" using x_props by auto
            then have upper: "(\<tau> \<sigma> x - \<tau> \<sigma> i) \<le> (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
            then have "memR I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
              using k_mem memR_antimono by blast
            then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms c_props lower by auto
            then have "Formula.sat \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{c..<k}. Formula.sat \<sigma> V v x \<psi>" by auto
          moreover have "mem (int_remove_lower_bound I1) (\<tau> \<sigma> k - \<tau> \<sigma> c)"
            using k_mem c_props
            by (metis atLeastLessThan_iff int_remove_lower_bound.rep_eq interval_geq less_or_eq_imp_le memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
          ultimately have c_sat: "Formula.sat \<sigma> V v c (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
            using assms k_cond
            by auto
          {
            assume "(c-1) \<in> B"
            then have "c-1\<ge>c" using c_def B_props by auto
            moreover have "c-1 < c" using c_pos by auto
            ultimately have "False" by auto
          }
          then have "(c-1) \<notin> B" by blast
          then have disj: "(c-1)\<notin>{i..<k} \<or> \<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>Formula.sat \<sigma> V v (c-1) \<psi>" using B_def by blast
          {
            assume "(c-1)\<notin>{i..<k}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c-1)\<notin>{i..<k})"
            then have c_pred_geq_i: "(c-1)\<in>{i..<k}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>Formula.sat \<sigma> V v (c-1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              then have "\<not>Formula.sat \<sigma> V v (c-1) \<psi>" using disj by blast
              then have "False"
                using k_greater_sat c_pred_geq_i c_suc_mem
                by auto
            }
            moreover {
              assume c_pred_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              {
                assume "\<not>mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
                then have upper: "\<not> memR I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
                  using c_pred_not_mem_1 assms geq_j_mem k_cond k_props
                  by auto
                have "\<tau> \<sigma> c \<ge> \<tau> \<sigma> (c-1)" by auto
                then have "\<tau> \<sigma> c - \<tau> \<sigma> i \<ge> \<tau> \<sigma> (c-1) - \<tau> \<sigma> i" using diff_le_mono by blast
                moreover have "memR I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" using c_props assms by auto
                ultimately have "memR I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" using memR_antimono by blast
                then have "False" using upper by auto
              }
              then have "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by blast
              then have "(c-1)\<ge>i" "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v (c-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
                using c_pred_geq_i c_sat interval_all c_pos
                by auto
              then have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
                using interval_all sat_eventually
                by blast
            }
            ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by auto
          }
          ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by blast
        }
        ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
          by blast
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by blast
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using release
    by auto
  then show "Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
    using assms I2_def release_safe_bounded_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def release_safe_bounded_def
    by auto
  then have eventually: "Formula.sat \<sigma> V v i (eventually I1 Formula.TT)" by auto
  then have "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (eventually I2 \<phi>) \<or> Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    using assm
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>)"
    then have "Formula.sat \<sigma> V v i (always I1 \<psi>)"
      using assms always_rewrite_bounded[of I1 \<sigma> V v i \<psi>]
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (eventually I2 \<phi>)"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j \<phi>" by blast
    {
      fix x
      assume x_props: "x\<ge>i" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume "x\<le>j"
        then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using j_props assms I2_def flip_int_less_lower_props
          by (meson diff_le_mono memL_mono memR_antimono memR_zero zero_le)
        then have "False" using x_props assms I2_def
          using flip_int_less_lower.rep_eq memR.rep_eq memR_zero
          by auto
      }
      then have "\<not>(x\<le>j)" by blast
      then have "x>j" by auto
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> x>j" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume until: "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by blast
    then have j_pred_sat: "Formula.sat \<sigma> V v (j+1) (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))" by auto
    then have "\<exists>x\<ge>(j+1). Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>) \<and> (\<forall>k\<in>{(j+1)..<x}. Formula.sat \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<ge>(j+1)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)" "\<forall>k\<in>{(j+1)..<x}. Formula.sat \<sigma> V v k \<psi>" by blast
    {
      fix l
      assume l_props: "l\<ge>i"
      {
        assume "l>x"
        then have "\<exists>k \<in> {i ..< l}. Formula.sat \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l>x)" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
        then have l_props: "x\<ge>l" "l\<ge>i" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using l_props by auto
        {
          assume "l\<ge>(j+1)"
          then have "Formula.sat \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<ge>(j+1)"
          then have l_geq: "l\<le>(j+1)" by auto
          have j_suc_psi: "Formula.sat \<sigma> V v (j+1) \<psi>" using j_pred_sat by auto
          {
            assume "l<(j+1)"
            then have "\<tau> \<sigma> l \<le> \<tau> \<sigma> j" by auto
            then have "mem I2 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using assms I2_def j_props flip_int_less_lower_props
            by (meson diff_le_mono le0 memL_mono memR_antimono memR_zero)
            then have "\<not>mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
              using assms I2_def flip_int_less_lower.rep_eq memR.rep_eq memR_zero
              by auto
            then have "False" using l_assms by auto
          }
          then have "l=(j+1)" using l_geq le_eq_less_or_eq by blast
          then have "Formula.sat \<sigma> V v l \<psi>" using j_suc_psi by blast
        }
        ultimately have "Formula.sat \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {i ..< l}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>)" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by blast
  then show "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
    using assm
    by auto
qed

lemma sat_and_release_rewrite:
  assumes "bounded I" "\<not>mem I 0" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>')) = Formula.sat \<sigma> V v i (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
proof (cases "\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)")
  case True
  then have eventually: "sat \<sigma> V v i (eventually I TT)"
    by auto
  then have "sat \<sigma> V v i (Release \<phi>' I \<psi>') = sat \<sigma> V v i (release_safe_bounded \<phi>' I \<psi>')"
    using sat_release_rewrite[OF assms, of \<sigma> V v i \<phi>' \<psi>']
    by auto
  moreover have "
    sat \<sigma> V v i (Or (And \<phi> (Neg (eventually I TT))) (And \<phi> (release_safe_bounded \<phi>' I \<psi>'))) =
    sat \<sigma> V v i (And \<phi> (release_safe_bounded \<phi>' I \<psi>'))"
    using eventually
    by auto
  ultimately show ?thesis
    unfolding and_release_safe_bounded_def
    by auto
qed (auto simp add: and_release_safe_bounded_def)

(* end rewrite formulas *)

lemma release_safe_0_future_bounded[simp]: "Formula.future_bounded (release_safe_0 \<phi> I \<psi>) = (bounded I \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: release_safe_0_def)

lemma sat_convert_multiway: "safe_formula \<phi> \<Longrightarrow> sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> sat \<sigma> V v i \<phi>"
proof (induction \<phi> arbitrary: V v i rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "get_and_list (convert_multiway \<psi>)"
  let ?sat = "sat \<sigma> V v i"
  have b_def: "?b = Ands (?la @ ?lb)" using And_safe by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_safe sat_get_and by blast
  moreover have "list_all ?sat ?lb \<longleftrightarrow> ?sat \<psi>" using And_safe sat_get_and by blast
  ultimately show ?case using And_safe by (auto simp: list.pred_set)
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "convert_multiway \<psi>"
  let ?sat = "sat \<sigma> V v i"
  have b_def: "?b = Ands (Neg ?lb # ?la)" using And_Not by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_Not sat_get_and by blast
  then show ?case using And_Not by (auto simp: list.pred_set)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Trigger \<phi>' I \<psi>'"

  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have get_and_list: "get_and_list (convert_multiway t) = [convert_multiway t]"
    unfolding t_def
    by auto

  show ?case
  proof (cases "safe_formula t")
    case True
    then obtain l where l_props:
      "convert_multiway (And \<phi> t) = Ands l"
      "set l = set (get_and_list (convert_multiway \<phi>)) \<union> {convert_multiway t}"
      using t_not_safe_assign t_not_constraint get_and_list
      by simp
  
    have t_sat: "sat \<sigma> V v i (convert_multiway t) = sat \<sigma> V v i t"
      using And_Trigger(6-7)
      unfolding t_def
      by auto
  
    have "(\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>) = sat \<sigma> V v i (And \<phi> (Trigger \<phi>' I \<psi>'))"
    proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
      case True
      then obtain l' where l'_props: "convert_multiway \<phi> = Ands l'" by (auto split: formula.splits)
      then have "get_and_list (convert_multiway \<phi>) = l'"
        by auto
      moreover have "(\<forall>\<phi> \<in> set l'. sat \<sigma> V v i \<phi>) = sat \<sigma> V v i \<phi>"
        using And_Trigger(5) l'_props
        by auto
      ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
    next
      case False
      then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
        by (auto split: formula.splits)
      moreover have "sat \<sigma> V v i (convert_multiway \<phi>) = sat \<sigma> V v i \<phi>"
        using And_Trigger(5)
        by auto
      ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
    qed
  
    then show ?thesis
      using l_props(1)
      unfolding t_def
      by auto
  next
    case False
    then show ?thesis
      using And_Trigger t_not_safe_assign t_not_constraint
      unfolding t_def
      by auto
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  then show ?case using sat_and_release_rewrite[OF And_Release(5-6)] by auto
next
  case (Agg y \<omega> b f \<phi>)
  then show ?case
    by (simp add: nfv_def fv_convert_multiway cong: conj_cong)
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  then have "\<forall>V v i. sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> sat \<sigma> V v i \<phi>"
  proof -
    {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis by (cases \<phi>) (auto simp add: safe_assignment_def)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> (\<forall>V v i. sat \<sigma> V v i (convert_multiway \<phi>') = sat \<sigma> V v i \<phi>') | _ \<Rightarrow> False)"
      then have ?thesis by (cases \<phi>) (auto)
    }
    ultimately show ?thesis using assms by auto
  qed
  then show ?case using assms(5) by auto
next
  case assms: (Release_0 \<phi> I \<psi>)
  then show ?case using sat_release_rewrite_0 by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (Ands l pos neg)
  then have l_future_bounded: "list_all (\<lambda>a. sat \<sigma> V v i (convert_multiway a) = sat \<sigma> V v i a) l"
  proof -
    {
      fix \<phi>
      assume assm: "\<phi> \<in> set l"
      then have "sat \<sigma> V v i (convert_multiway \<phi>) = sat \<sigma> V v i \<phi>"
      proof (cases "\<phi> \<in> set pos")
        case True
        then show ?thesis using Ands(6) by (auto simp add: list_all_iff)
      next
        case False
        then have \<phi>'_props: "case \<phi> of Neg \<phi>' \<Rightarrow> \<forall>x xa xaa. sat \<sigma> x xa xaa (convert_multiway \<phi>') = sat \<sigma> x xa xaa \<phi>'
           | _ \<Rightarrow> \<forall>x xa xaa. sat \<sigma> x xa xaa (convert_multiway \<phi>) = sat \<sigma> x xa xaa \<phi>"
          using Ands(1,7) assm
          by (auto simp add: list_all_iff)
        then show ?thesis
          by (cases \<phi>) (auto split: if_splits formula.splits)
      qed
    }
    then show ?thesis by (auto simp add: list_all_iff)
  qed
  then show ?case by (auto simp add: list_all_iff)
qed (auto cong: nat.case_cong)

end (*context*)

interpretation Formula_slicer: abstract_slicer "relevant_events \<phi>" for \<phi> .

lemma sat_slice_iff:
  assumes "v \<in> S"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (Formula_slicer.slice \<phi> S \<sigma>) V v i \<phi>"
  by (rule sat_slice_strong[OF assms]) auto

lemma Neg_splits:
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | \<phi> \<Rightarrow> g \<phi>) =
   ((\<forall>\<psi>. \<phi> = formula.Neg \<psi> \<longrightarrow> P (f \<psi>)) \<and> ((\<not> Formula.is_Neg \<phi>) \<longrightarrow> P (g \<phi>)))"
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> g \<phi>) =
   (\<not> ((\<exists>\<psi>. \<phi> = formula.Neg \<psi> \<and> \<not> P (f \<psi>)) \<or> ((\<not> Formula.is_Neg \<phi>) \<and> \<not> P (g \<phi>))))"
  by (cases \<phi>; auto simp: Formula.is_Neg_def)+

fun map_formula :: "(Formula.formula \<Rightarrow> Formula.formula) \<Rightarrow> Formula.formula \<Rightarrow> Formula.formula" where
  "map_formula f (Formula.Pred r ts) = f (Formula.Pred r ts)"
| "map_formula f (Formula.Let p \<phi> \<psi>) = f (
    Formula.Let p (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Eq t1 t2) = f (Formula.Eq t1 t2)"
| "map_formula f (Formula.Less t1 t2) = f (Formula.Less t1 t2)"
| "map_formula f (Formula.LessEq t1 t2) = f (Formula.LessEq t1 t2)"
| "map_formula f (Formula.Neg \<phi>) = f (Formula.Neg (map_formula f \<phi>))"
| "map_formula f (Formula.Or \<phi> \<psi>) = f (
    Formula.Or (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.And \<phi> \<psi>) = f (
    Formula.And (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Ands \<phi>s) = f (
    Formula.Ands (map (map_formula f) \<phi>s)
  )"
| "map_formula f (Formula.Exists \<phi>) = f (Formula.Exists (map_formula f \<phi>))"
| "map_formula f (Formula.Agg y \<omega> b f' \<phi>) = f (
    Formula.Agg y \<omega> b f' (map_formula f \<phi>)
  )"
| "map_formula f (Formula.Prev I \<phi>) = f (Formula.Prev I (map_formula f \<phi>))"
| "map_formula f (Formula.Next I \<phi>) = f (Formula.Next I (map_formula f \<phi>))"
| "map_formula f (Formula.Since \<phi> I \<psi>) = f (
    Formula.Since (map_formula f \<phi>) I ( map_formula f \<psi>)
  )"
| "map_formula f (Formula.Until \<phi> I \<psi>) = f (
    Formula.Until (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Trigger \<phi> I \<psi>) = f (
    Formula.Trigger (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Release \<phi> I \<psi>) = f (
    Formula.Release (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.MatchF I r) = f (Formula.MatchF I r)"
| "map_formula f (Formula.MatchP I r) = f (Formula.MatchP I r)"

lemma map_formula_fvi:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  shows "Formula.fvi b (map_formula f \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi> arbitrary: b) qed (auto simp add: assms release_safe_0_def always_safe_0_def fvi.simps(17))

(*lemma map_formula_safe:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  assumes "\<And>\<phi>. safe_formula (f \<phi>) = safe_formula \<phi>"
  assumes "\<And>\<phi>. \<not>safe_formula \<phi> \<Longrightarrow> f \<phi> = \<phi>"
  shows "safe_formula (map_formula f \<phi>) = safe_formula \<phi>"
proof (induction \<phi> rule: safe_formula.induct)
  case (6 p \<phi> \<psi>)
  then show ?case by (auto simp add: map_formula_fvi[OF assms(1)] assms(2-3))
next
  case ("7_1" v va)
  then show ?case
    using map_formula_fvi[OF assms(1)] assms
    sorry

qed (auto simp add: map_formula_fvi[OF assms(1)] assms(2-3))*)
 

lemma map_formula_sat:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  assumes "\<And>\<sigma> V v i \<phi>. Formula.sat \<sigma> V v i (f \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  shows "\<And>\<sigma> V v i. Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V v i (map_formula f \<phi>)"
using assms proof (induction \<phi>)
  case assm: (Let p \<phi>' \<psi>')
  from assms have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
    using Formula.nfv_def map_formula_fvi
    by auto
  {
    fix \<sigma> V v i
    have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi>' \<and> Formula.sat \<sigma> V v i \<phi>'})) v i \<psi>'"
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi>' \<and> Formula.sat \<sigma> V v i \<phi>'})) v i (map_formula f \<psi>')"
      using assm
      by blast
    then have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> V v i (map_formula f (formula.Let p \<phi>' \<psi>'))"
      using assm nfv_eq assms
      by auto
  }
  then show ?case by blast
next
  case assm: (Agg y \<omega> b f' \<phi>')
  {
    fix \<sigma> V v i
    define M where "M = {(x, ecard Zs) |
        x Zs. Zs = {zs. length zs = b \<and>
        Formula.sat \<sigma> V (zs @ v) i \<phi>' \<and>
        Formula.eval_trm (zs @ v) f' = x} \<and> Zs \<noteq> {}
    }"
    define M' where "M' = {(x, ecard Zs) |
        x Zs. Zs = {zs. length zs = b \<and>
        Formula.sat \<sigma> V (zs @ v) i (map_formula f \<phi>') \<and>
        Formula.eval_trm (zs @ v) f' = x} \<and> Zs \<noteq> {}
    }"
    have M_eq: "M = M'" using M_def M'_def assm by auto
    have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
      using assms Formula.nfv_def map_formula_fvi
      by auto
    have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = (
      (M = {} \<longrightarrow> fv \<phi>' \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M
    )"
      using M_def
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = (
      (M' = {} \<longrightarrow> fv (map_formula f \<phi>') \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M')"
      using assms assm M_eq nfv_eq map_formula_fvi
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' (map_formula f \<phi>'))"
      using M'_def
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = Formula.sat \<sigma> V v i (map_formula f (formula.Agg y \<omega> b f' \<phi>'))"
      using assms by auto
  }
  then show ?case by blast
qed (auto split: nat.split)


fun rewrite_trigger :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite_trigger (Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)) = (
    if (mem I 0) then
      \<comment> \<open>the rewrite function already was applied recursively, hence the trigger should already be rewritten\<close>
      Formula.And \<phi> ( trigger_safe_0 \<alpha> I \<beta>)
    else (
      if (bounded I) then
        and_trigger_safe_bounded \<phi> \<alpha> I \<beta>
      else
        and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>
    )
  )"
| "rewrite_trigger (Formula.Trigger \<alpha> I \<beta>) = (
    if (mem I 0) then
      trigger_safe_0 \<alpha> I \<beta>
    else (
      Formula.Trigger \<alpha> I \<beta>
    )
  )"
| "rewrite_trigger f = f"

lemma historically_safe_0_fvi[simp]: "Formula.fvi b (historically_safe_0 I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_0_def split: if_splits)

lemma historically_safe_unbounded_fvi[simp]: "Formula.fvi b (historically_safe_unbounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_bounded_fvi[simp]: "Formula.fvi b (historically_safe_bounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma trigger_safe_0_fvi[simp]: "Formula.fvi b (trigger_safe_0 \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_0_def split: if_splits)

lemma trigger_safe_unbounded_fvi[simp]: "Formula.fvi b (trigger_safe_unbounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_unbounded_def)

lemma trigger_safe_bounded_fvi[simp]: "Formula.fvi b (trigger_safe_bounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_bounded_def)

lemma rewrite_trigger_fvi[simp]: "Formula.fvi b (rewrite_trigger \<phi>) = Formula.fvi b \<phi>"
proof (cases \<phi>)
  case (And \<phi> \<psi>)
  then show ?thesis
  proof (cases \<psi>)
    case (Trigger \<alpha> I \<beta>)
    then show ?thesis
    proof (cases "mem I 0")
      case True
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> ( trigger_safe_0 \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        unfolding And
        using Trigger
        by auto
    next
      case not_mem: False
      show ?thesis
      proof (cases "bounded I")
        case True
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_bounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          unfolding and_trigger_safe_bounded_def once_def trigger_safe_bounded_def eventually_def historically_safe_bounded_def Formula.TT_def Formula.FF_def
          by auto
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          unfolding and_trigger_safe_unbounded_def once_def trigger_safe_unbounded_def eventually_def historically_safe_unbounded_def Formula.TT_def Formula.FF_def
          by auto
      qed
    qed
  qed (auto)
next
  case (Trigger \<alpha> I \<beta>)
  show ?thesis
  proof (cases "mem I 0")
    case True
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = trigger_safe_0 \<alpha> I \<beta>"
      by auto
    show ?thesis
      unfolding Trigger rewrite
      by auto
  next
    case False
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = formula.Trigger \<alpha> I \<beta>"
      by auto
    then show ?thesis unfolding Trigger by auto
  qed
qed (auto)

lemma rewrite_trigger_sat[simp]: "Formula.sat \<sigma> V v i (rewrite_trigger \<phi>) = Formula.sat \<sigma> V v i \<phi>"
proof (cases \<phi>)
  case (And \<phi> \<psi>)
  then show ?thesis
  proof (cases \<psi>)
    case (Trigger \<alpha> I \<beta>)
    then show ?thesis
    proof (cases "mem I 0")
      case True
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (trigger_safe_0 \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        unfolding And Trigger
        using sat_trigger_rewrite_0[OF True]
        by auto
    next
      case not_mem: False
      show ?thesis
      proof (cases "bounded I")
        case True
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_bounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          using sat_and_trigger_bounded_rewrite[OF True not_mem]
          by auto
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          using sat_and_trigger_unbounded_rewrite[OF False not_mem]
          by auto
      qed
    qed
  qed (auto)
next
  case (Trigger \<alpha> I \<beta>)
  show ?thesis
  proof (cases "mem I 0")
    case True
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = trigger_safe_0 \<alpha> I \<beta>"
      by auto
    show ?thesis
      unfolding Trigger rewrite
      using sat_trigger_rewrite_0[OF True]
      by auto
  next
    case False
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = formula.Trigger \<alpha> I \<beta>"
      by auto
    then show ?thesis unfolding Trigger by auto
  qed
qed (auto)

lemma trigger_not_safe_assignment: "\<not> safe_assignment (fv \<phi>) (formula.Trigger \<alpha> I \<beta>)"
  unfolding safe_assignment_def
  by auto

lemma rewrite_trigger_safe_formula[simp]: 
  assumes safe: "safe_formula \<phi>"
  shows "safe_formula (rewrite_trigger \<phi>)"
using assms
proof (cases \<phi>)
  case (And \<phi> \<psi>)
  then show ?thesis
  using assms
  proof (cases \<psi>)
    case (Trigger \<alpha> I \<beta>)
    then show ?thesis
    proof (cases "mem I 0")
      case True
      then have rewrite: "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (trigger_safe_0 \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      have "safe_formula_dual False safe_formula \<alpha> I \<beta>"
        using safe True
        unfolding And Trigger
        by (auto simp add: safe_assignment_def safe_formula_dual_def split: if_splits)
      then have "safe_formula (trigger_safe_0 \<alpha> I \<beta>)"
        using True
        unfolding safe_formula_dual_def trigger_safe_0_def
        by (auto) (auto split: formula.splits)
      then show ?thesis
        using safe
        unfolding And rewrite
        by auto
    next
      case not_mem: False
      show ?thesis
      proof (cases "bounded I")
        case True
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_bounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          using safe trigger_not_safe_assignment
          unfolding And Trigger and_trigger_safe_bounded_def trigger_safe_bounded_def
          by (auto split: if_splits simp add: safe_formula_dual_def)
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          using safe trigger_not_safe_assignment
          unfolding And Trigger and_trigger_safe_unbounded_def trigger_safe_unbounded_def
          by (auto split: if_splits simp add: safe_formula_dual_def)
      qed
    qed
  qed (auto)
next
  case (Trigger \<alpha> I \<beta>)
  show ?thesis
  proof (cases "mem I 0")
    case True
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = trigger_safe_0 \<alpha> I \<beta>"
      by auto
    show ?thesis
      using safe
      unfolding Trigger rewrite trigger_safe_0_def
      by (auto simp add: safe_formula_dual_def split: if_splits) (auto split: formula.splits)
  next
    case False
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = formula.Trigger \<alpha> I \<beta>"
      by auto
    then show ?thesis
      using safe
      unfolding Trigger
      by auto
  qed
qed (auto)

(*<*)
end
(*>*)
