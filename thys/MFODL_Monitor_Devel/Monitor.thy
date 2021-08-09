(*<*)
theory Monitor
  imports
    Formula
    Optimized_Join
    "MFOTL_Monitor_Devel.Abstract_Monitor"
    "HOL-Library.While_Combinator"
    "HOL-Library.Mapping"
    "Deriving.Derive"
    "Generic_Join_Devel.Generic_Join_Correctness"
begin
(*>*)

section \<open>Generic monitoring algorithm\<close>

text \<open>The algorithm defined here abstracts over the implementation of the temporal operators.\<close>

subsection \<open>Monitorable formulas\<close>

definition "mmonitorable \<phi> \<longleftrightarrow> safe_formula \<phi> \<and> Formula.future_bounded \<phi>"
definition "mmonitorable_regex b g r \<longleftrightarrow> safe_regex b g r \<and> Regex.pred_regex Formula.future_bounded r"

definition is_simple_eq :: "Formula.trm \<Rightarrow> Formula.trm \<Rightarrow> bool" where
  "is_simple_eq t1 t2 = (Formula.is_Const t1 \<and> (Formula.is_Const t2 \<or> Formula.is_Var t2) \<or>
    Formula.is_Var t1 \<and> Formula.is_Const t2)"

function (sequential) mmonitorable_exec :: "Formula.formula \<Rightarrow> bool" where
  "mmonitorable_exec (Formula.Eq t1 t2) = is_simple_eq t1 t2"
| "mmonitorable_exec (Formula.Neg (Formula.Eq (Formula.Var x) (Formula.Var y))) = (x = y)"
| "mmonitorable_exec (Formula.Pred e ts) = list_all (\<lambda>t. Formula.is_Var t \<or> Formula.is_Const t) ts"
| "mmonitorable_exec (Formula.Let p \<phi> \<psi>) = ({0..<Formula.nfv \<phi>} \<subseteq> Formula.fv \<phi> \<and> mmonitorable_exec \<phi> \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.Neg \<phi>) = (fv \<phi> = {} \<and> mmonitorable_exec \<phi>)"
| "mmonitorable_exec (Formula.Or \<phi> \<psi>) = (fv \<phi> = fv \<psi> \<and> mmonitorable_exec \<phi> \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.And \<phi> \<psi>) = (mmonitorable_exec \<phi> \<and>
    (safe_assignment (fv \<phi>) \<psi> \<or> mmonitorable_exec \<psi> \<or>
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Formula.Neg \<psi>' \<Rightarrow> mmonitorable_exec \<psi>'
        | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True mmonitorable_exec \<phi>' I \<psi>'
        | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> (
          bounded I \<and> \<not>mem I 0 \<and>
          mmonitorable_exec \<phi>' \<and> mmonitorable_exec \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
          mmonitorable_exec (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
        )
        | _ \<Rightarrow> False
      ))))"
| "mmonitorable_exec (Formula.Ands l) = (let (pos, neg) = partition mmonitorable_exec l in
    pos \<noteq> [] \<and> list_all (\<lambda>\<phi>. (case \<phi> of
        (Formula.Neg \<phi>') \<Rightarrow> mmonitorable_exec \<phi>'
        | _ \<Rightarrow> mmonitorable_exec \<phi>
      )
    ) neg \<and>
    \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos)))"
| "mmonitorable_exec (Formula.Exists \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (Formula.Agg y \<omega> b f \<phi>) = (mmonitorable_exec \<phi> \<and>
    y + b \<notin> Formula.fv \<phi> \<and> {0..<b} \<subseteq> Formula.fv \<phi> \<and> Formula.fv_trm f \<subseteq> Formula.fv \<phi>)"
| "mmonitorable_exec (Formula.Prev I \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (Formula.Next I \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (Formula.Since \<phi> I \<psi>) = (Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and>
    (mmonitorable_exec \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)) \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.Until \<phi> I \<psi>) = (Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and> bounded I \<and>
    (mmonitorable_exec \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)) \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (Formula.Trigger \<phi> I \<psi>) = safe_formula_dual False mmonitorable_exec \<phi> I \<psi>"
| "mmonitorable_exec (Formula.Release \<phi> I \<psi>) = (mem I 0 \<and> bounded I \<and> mmonitorable_exec \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> mmonitorable_exec (release_safe_0 \<phi> I \<psi>))"
| "mmonitorable_exec (Formula.MatchP I r) = Regex.safe_regex Formula.fv (\<lambda>g \<phi>. mmonitorable_exec \<phi> \<or> (g = Lax \<and> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False))) Past Strict r"
| "mmonitorable_exec (Formula.MatchF I r) = (Regex.safe_regex Formula.fv (\<lambda>g \<phi>. mmonitorable_exec \<phi> \<or> (g = Lax \<and> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False))) Futu Strict r \<and> bounded I)"
| "mmonitorable_exec _ = False"
  by pat_completeness auto
termination
  using size'_and_release size'_Release size'_Or size'_release_aux
  by (relation "measure size'") 
     (auto simp add: Nat.less_Suc_eq_le release_safe_0_def dest!: sum_list_mem_leq[of _ _ size'] regex_atms_size')


lemma cases_Neg_iff:
  "(case \<phi> of formula.Neg \<psi> \<Rightarrow> P \<psi> | _ \<Rightarrow> False) \<longleftrightarrow> (\<exists>\<psi>. \<phi> = formula.Neg \<psi> \<and> P \<psi>)"
  by (cases \<phi>) auto

lemma safe_formula_mmonitorable_exec: "safe_formula \<phi> \<Longrightarrow> Formula.future_bounded \<phi> \<Longrightarrow> mmonitorable_exec \<phi>"
proof (induct \<phi> rule: safe_formula.induct)
  case (9 \<phi> \<psi>)
  then show ?case
  proof (cases "fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>'
      | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
      | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> (
        bounded I \<and> \<not>mem I 0 \<and>
        safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
        safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
      )
      | _ \<Rightarrow> False
    ))")
    case True
    then have fvs: "fv \<psi> \<subseteq> fv \<phi>"
      by auto
    show ?thesis
      using True 9
    proof (cases "is_constraint \<psi>")
      case False
      then have \<psi>_props: "(case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>'
        | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> (
          bounded I \<and> \<not>mem I 0 \<and>
          safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
          safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
        )
        | _ \<Rightarrow> False
      )" using True
        by auto
      then show ?thesis
      proof (cases "case \<psi> of Formula.Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False")
        case True
        then obtain \<psi>' where "\<psi> = Formula.Neg \<psi>'" "safe_formula \<psi>'"
          by (auto split:formula.splits)
        then show ?thesis using 9 \<psi>_props by (auto split: formula.splits)
      next
        case f1: False
        then show ?thesis
        proof (cases "case \<psi> of Formula.Trigger \<phi>' I \<psi>' \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> False")
          case True
          then obtain \<phi>' I \<psi>' where "\<psi> = Formula.Trigger \<phi>' I \<psi>'" "safe_formula_dual True safe_formula \<phi>' I \<psi>'"
            using \<psi>_props
            by (auto split:formula.splits)
          then show ?thesis using 9 \<psi>_props by (auto simp add: safe_formula_dual_def)
        next
          case False
          then obtain \<phi>' I \<psi>' where release_props:
            "\<psi> = Formula.Release \<phi>' I \<psi>'"
            "bounded I"
            "\<not>mem I 0"
            "safe_formula \<phi>'"
            "safe_formula \<psi>'"
            "fv \<phi>' = fv \<psi>'"
            "safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            using f1 \<psi>_props
            by (auto split:formula.splits)
          
          have safe: "safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            unfolding and_release_safe_bounded_def
            using safe_formula_release_bounded release_props fvs release_fvi(2) 9(8)
            by (auto)
          
          have bounded: "Formula.future_bounded (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            using release_bounded_future_bounded[of \<phi>' I \<psi>'] release_props(1-3) 9(9)
            by (auto simp add: and_release_safe_bounded_def)
          have "mmonitorable_exec (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            using 9(7)[OF release_props(1) safe bounded]
            by auto
          then show ?thesis using 9 release_props by (auto simp add: safe_assignment_def)
        qed
        
      qed
    qed (auto)
  qed (auto)
next
  case (10 l)
  from "10.prems"(2) have bounded: "Formula.future_bounded \<phi>" if "\<phi> \<in> set l" for \<phi>
    using that by (auto simp: list.pred_set)
  obtain poss negs where posnegs: "(poss, negs) = partition safe_formula l" by simp
  obtain posm negm where posnegm: "(posm, negm) = partition mmonitorable_exec l" by simp
  have "set poss \<subseteq> set posm"
  proof (rule subsetI)
    fix x assume "x \<in> set poss"
    then have "x \<in> set l" "safe_formula x" using posnegs by simp_all
    then have "mmonitorable_exec x" using "10.hyps"(1) bounded by blast
    then show "x \<in> set posm" using \<open>x \<in> set poss\<close> posnegm posnegs by simp
  qed
  then have "set negm \<subseteq> set negs" using posnegm posnegs by auto
  obtain s_props: "poss \<noteq> []" "list_all (\<lambda>\<phi>. (case \<phi> of
        Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) negs"
    "(\<Union>x\<in>set negs. fv x) \<subseteq> (\<Union>x\<in>set poss. fv x)"
    using "10.prems"(1) posnegs by simp
  then have "posm \<noteq> []" using \<open>set poss \<subseteq> set posm\<close> by auto
  moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
        Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>'
        | _ \<Rightarrow> mmonitorable_exec \<phi>
      )
    ) negm"
  proof -
    have "\<And>\<phi>. \<phi> \<in> set negm \<Longrightarrow> (case \<phi> of
        Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>'
        | _ \<Rightarrow> mmonitorable_exec \<phi>
      )"
    proof -
      fix x assume "x \<in> set negm"
      then have x_mem: "x \<in> set negs" using \<open>set negm \<subseteq> set negs\<close> by blast
      then have x_props: "(case x of
          Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | _ \<Rightarrow> safe_formula x
        )"
        using s_props(2)
        by (simp add: list_all_def)
      show "case x of
        Formula.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>'
        | _ \<Rightarrow> mmonitorable_exec x"
      proof (cases "\<exists>z. x = Formula.Neg z")
        case True
        then obtain z where z_props: "x = Formula.Neg z" "safe_formula z" using x_props by auto
        then show ?thesis
          using "10.hyps"(7)[OF posnegs refl x_mem z_props] posnegs bounded[of x] x_mem
          by (auto simp add: o_def split: formula.splits)
      next
        case not_neg: False
        then have safe: "safe_formula x"
          using not_neg x_props
          by (auto split: formula.splits)
        have x_mem: "x \<in> set l"
          using posnegs x_mem
          by auto
        have "mmonitorable_exec x" using 10(1)[OF x_mem safe] posnegs bounded[OF x_mem] by auto
        then show ?thesis using \<open>x \<in> set negm\<close> posnegm by auto
      qed
    qed
    then show ?thesis by (simp add: list_all_iff)
  qed
  moreover have "(\<Union>x\<in>set negm. fv x) \<subseteq> (\<Union>x\<in>set posm. fv x)"
    using \<open>\<Union> (fv ` set negs) \<subseteq> \<Union> (fv ` set poss)\<close> \<open>set poss \<subseteq> set posm\<close> \<open>set negm \<subseteq> set negs\<close>
    by fastforce
  ultimately show ?case using posnegm by simp
next
  case (19 I r)
  then show ?case
    by (auto elim!: safe_regex_mono[rotated] simp: cases_Neg_iff regex.pred_set)
next
  case (20 I r)
  then show ?case
    by (auto elim!: safe_regex_mono[rotated] simp: cases_Neg_iff regex.pred_set)
qed (auto simp add: is_simple_eq_def list.pred_set cases_Neg_iff safe_formula_dual_def split: if_splits)

lemma safe_assignment_future_bounded: "safe_assignment X \<phi> \<Longrightarrow> Formula.future_bounded \<phi>"
  unfolding safe_assignment_def by (auto split: formula.splits)

lemma is_constraint_future_bounded: "is_constraint \<phi> \<Longrightarrow> Formula.future_bounded \<phi>"
  by (induction rule: is_constraint.induct) simp_all

lemma mmonitorable_exec_mmonitorable: "mmonitorable_exec \<phi> \<Longrightarrow> mmonitorable \<phi>"
proof (induct \<phi> rule: mmonitorable_exec.induct)
  case (7 \<phi> \<psi>)
  show ?case
  proof (cases "\<exists>\<psi>'. \<psi> = Formula.Neg \<psi>'")
    case True
    then show ?thesis
      using 7
      unfolding mmonitorable_def
      by (auto intro: safe_assignment_future_bounded is_constraint_future_bounded)
  next
    case non_neg: False
    then show ?thesis
    proof (cases "\<exists>\<phi>' I \<psi>'. \<psi> = Formula.Trigger \<phi>' I \<psi>'")
      case True
      then obtain \<phi>' I \<psi>' where \<psi>_def: "\<psi> = Formula.Trigger \<phi>' I \<psi>'"
        by blast
      then show ?thesis
        using 7(1-2,8) 7(4)[OF \<psi>_def]
        unfolding mmonitorable_def
        by (auto simp add: safe_assignment_def safe_formula_dual_def intro: is_constraint_future_bounded)
    next
      case no_trigger: False
      show ?thesis
      proof (cases "\<exists>\<phi>' I \<psi>'. \<psi> = Formula.Release \<phi>' I \<psi>'")
        case True
        then obtain \<phi>' I \<psi>' where \<psi>_def: "\<psi> = Formula.Release \<phi>' I \<psi>'"
          by blast
        have \<phi>_props: "mmonitorable \<phi>"
          using 7(1,8)
          by auto
        
        show ?thesis
        proof (cases "mmonitorable_exec \<psi>")
          case True
          then have \<psi>_props: "safe_formula \<psi> \<and> Formula.future_bounded \<psi>"
            using 7(2)
            unfolding mmonitorable_def
            by auto
          then have "mem I 0" "bounded I" "fv \<phi>' \<subseteq> fv \<psi>'"
            unfolding \<psi>_def
            by auto
          then show ?thesis
            using \<phi>_props \<psi>_props
            unfolding mmonitorable_def
            by (auto simp add: safe_assignment_def)
        next
          case False
          then have "fv (formula.Release \<phi>' I \<psi>') \<subseteq> fv \<phi>"
            using 7(8) \<phi>_props
            unfolding mmonitorable_exec.simps \<psi>_def
            by (auto simp add: safe_assignment_def)

          moreover have "bounded I \<and> \<not>mem I 0 \<and>
            mmonitorable_exec \<phi>' \<and> mmonitorable_exec \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
            mmonitorable_exec (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
            using 7(8) False
            unfolding \<psi>_def
            by (auto simp add: safe_assignment_def)
         
          ultimately show ?thesis
            using 7(5-7)[OF \<psi>_def] \<phi>_props
            unfolding mmonitorable_def
            by (auto simp add: \<psi>_def)
        qed
      next
        case False
        then have "mmonitorable_exec \<phi> \<and> (safe_assignment (fv \<phi>) \<psi> \<or> mmonitorable_exec \<psi> \<or> fv \<psi> \<subseteq> fv \<phi> \<and> is_constraint \<psi>)"
          using non_neg no_trigger 7(8)
          by (auto split: formula.splits)
        then show ?thesis
          using non_neg 7
          unfolding mmonitorable_def
          by (auto intro: safe_assignment_future_bounded is_constraint_future_bounded)
      qed
    qed
  qed
next
  case (8 l)
  obtain poss negs where posnegs: "(poss, negs) = partition safe_formula l" by simp
  obtain posm negm where posnegm: "(posm, negm) = partition mmonitorable_exec l" by simp
  have pos_monitorable: "list_all mmonitorable_exec posm" using posnegm by (simp add: list_all_iff)
  have neg_monitorable: "list_all (\<lambda>\<phi>. (case \<phi> of
        (Formula.Neg \<phi>') \<Rightarrow> mmonitorable_exec \<phi>'
        | _ \<Rightarrow> mmonitorable_exec \<phi>
      )
    ) negm"
    using "8.prems" posnegm by (simp add: list_all_iff)
  have "set posm \<subseteq> set poss"
    using "8.hyps"(1) posnegs posnegm unfolding mmonitorable_def by auto
  then have neg_subset: "set negs \<subseteq> set negm"
    using posnegs posnegm by auto

  have list_all_mmonitorable:
    "list_all (\<lambda>\<phi>. (case \<phi> of
        (Formula.Neg \<phi>') \<Rightarrow> safe_formula \<phi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) negm"
    "list_all Formula.future_bounded negm"
  proof -
    {
      fix \<phi>
      assume assm: "\<phi> \<in> set negm"
      then have "case \<phi> of
        (Formula.Neg \<phi>') \<Rightarrow> mmonitorable \<phi>'
        | _ \<Rightarrow> mmonitorable \<phi>"
      proof (cases "\<exists>\<phi>'. \<phi> = Formula.Neg \<phi>'")
        case True
        then obtain \<phi>' where \<phi>_def: "\<phi> = Formula.Neg \<phi>'"
          by blast
        then have "mmonitorable_exec \<phi>'"
          using neg_monitorable assm
          by (auto split: formula.splits simp: list_all_iff)
        then show ?thesis
          using 8(7)[OF posnegm refl _ \<phi>_def] assm \<phi>_def
          unfolding mmonitorable_def
          by (auto split: formula.splits)
      next
        case no_neg: False
        moreover have "case \<phi> of
          (Formula.Neg \<phi>') \<Rightarrow> mmonitorable_exec \<phi>'
          | _ \<Rightarrow> mmonitorable_exec \<phi>"
          using neg_monitorable assm
          by (auto simp: list_all_iff)
        ultimately have "mmonitorable_exec \<phi>"
          using no_neg neg_monitorable assm
          by (auto split: formula.splits)
        then have "mmonitorable \<phi>"
          using 8(1)[of \<phi>] using assm posnegm
          by auto
        then show ?thesis using no_neg by (auto split: formula.splits)
      qed
    }
    then have \<phi>_props: "\<forall>\<phi> \<in> set negm. (case \<phi> of
      (Formula.Neg \<phi>') \<Rightarrow> mmonitorable \<phi>'
      | _ \<Rightarrow> mmonitorable \<phi>)"
      by auto
    {
      fix \<phi>
      assume "\<phi> \<in> set negm"
      then have \<phi>_props: "case \<phi> of
        (Formula.Neg \<phi>') \<Rightarrow> mmonitorable \<phi>'
        | _ \<Rightarrow> mmonitorable \<phi>"
        using \<phi>_props
        by auto

      then have "case \<phi> of
      (Formula.Neg \<phi>') \<Rightarrow> safe_formula \<phi>'
      | _ \<Rightarrow> safe_formula \<phi>"
        using safe_formula_dual_impl[of mmonitorable safe_formula]
        unfolding mmonitorable_def
        by (cases \<phi>) (auto)
    }
    then show "list_all (\<lambda>\<phi>. (case \<phi> of
      (Formula.Neg \<phi>') \<Rightarrow> safe_formula \<phi>'
      | _ \<Rightarrow> safe_formula \<phi>)) negm"
      by (auto simp: list_all_iff)

    {
      fix \<phi>
      assume "\<phi> \<in> set negm"
      then have \<phi>_props: "case \<phi> of
        (Formula.Neg \<phi>') \<Rightarrow> mmonitorable \<phi>'
        | _ \<Rightarrow> mmonitorable \<phi>"
        using \<phi>_props
        by auto

      have trigger_future_bounded: "\<And>\<phi> I \<psi>. safe_formula_dual True Formula.future_bounded \<phi> I \<psi> \<Longrightarrow> Formula.future_bounded (Formula.Trigger \<phi> I \<psi>)"
        unfolding safe_formula_dual_def mmonitorable_def
        by (auto split: if_splits formula.splits)

      then have "Formula.future_bounded \<phi>"
        using \<phi>_props
        unfolding mmonitorable_def
        by (cases \<phi>) (auto)
    }
    then show "list_all Formula.future_bounded negm"
      by (auto simp: list_all_iff)
  qed


  have "poss \<noteq> []" using "8.prems" posnegm \<open>set posm \<subseteq> set poss\<close> by auto
  moreover have "\<Union> (fv ` set negm) \<subseteq> \<Union> (fv ` set posm)"
    using "8.prems" posnegm by simp
  then have "\<Union> (fv ` set negs) \<subseteq> \<Union> (fv ` set poss)"
    using \<open>set posm \<subseteq> set poss\<close> \<open>set negs \<subseteq> set negm\<close> by fastforce
  ultimately have "safe_formula (Formula.Ands l)"
    using posnegs list_all_mmonitorable(1) neg_subset
    by (auto simp: list_all_iff)
  moreover have "Formula.future_bounded (Formula.Ands l)"
  proof -
    have "list_all Formula.future_bounded posm"
      using pos_monitorable "8.hyps"(1) posnegm unfolding mmonitorable_def
      by (auto elim!: list.pred_mono_strong)
    then have "list_all Formula.future_bounded l"
      using list_all_mmonitorable(2) posnegm
      by (auto simp: list_all_iff)
    then show ?thesis by (auto simp: list_all_iff)
  qed
  ultimately show ?case unfolding mmonitorable_def ..
next
  case (13 \<phi> I \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce simp: cases_Neg_iff)
next
  case (14 \<phi> I \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce simp: one_enat_def cases_Neg_iff)
next
  case (15 \<phi> I \<psi>)
  then show ?case
  proof (cases "mem I 0")
    case mem: True
    then show ?thesis
      using 15
      by (auto simp add: cases_Neg_iff mmonitorable_def safe_formula_dual_def split: if_splits)
  next
    case False
    then show ?thesis
      using 15
      by (auto simp add: cases_Neg_iff mmonitorable_def safe_formula_dual_def split: if_splits)
  qed
next
  case (16 \<phi> I \<psi>)
  then show ?case
  proof (cases "mem I 0")
    case mem: True
    then show ?thesis
      using 16
      by (auto simp add: cases_Neg_iff mmonitorable_def safe_formula_dual_def split: if_splits)
  next
    case False
    then show ?thesis
      using 16
      by (auto simp add: cases_Neg_iff mmonitorable_def safe_formula_dual_def split: if_splits)
  qed
next
  case (17 I r)
  then show ?case
    by (auto elim!: safe_regex_mono[rotated] dest: safe_regex_safe[rotated]
        simp: mmonitorable_regex_def mmonitorable_def cases_Neg_iff regex.pred_set)
next
  case (18 I r)
  then show ?case
    by (auto 0 3 elim!: safe_regex_mono[rotated] dest: safe_regex_safe[rotated]
        simp: mmonitorable_regex_def mmonitorable_def cases_Neg_iff regex.pred_set)
qed (auto simp add: mmonitorable_def mmonitorable_regex_def is_simple_eq_def one_enat_def list.pred_set split: if_splits)

lemma monitorable_formula_code[code]: "mmonitorable \<phi> = mmonitorable_exec \<phi>"
  using mmonitorable_exec_mmonitorable safe_formula_mmonitorable_exec mmonitorable_def
  by blast

subsection \<open>Handling regular expressions\<close>

datatype mregex =
  MSkip nat
  | MTestPos nat
  | MTestNeg nat
  | MPlus mregex mregex
  | MTimes mregex mregex
  | MStar mregex

primrec ok where
  "ok _ (MSkip n) = True"
| "ok m (MTestPos n) = (n < m)"
| "ok m (MTestNeg n) = (n < m)"
| "ok m (MPlus r s) = (ok m r \<and> ok m s)"
| "ok m (MTimes r s) = (ok m r \<and> ok m s)"
| "ok m (MStar r) = ok m r"

primrec from_mregex where
  "from_mregex (MSkip n) _ = Regex.Skip n"
| "from_mregex (MTestPos n) \<phi>s = Regex.Test (\<phi>s ! n)"
| "from_mregex (MTestNeg n) \<phi>s = (if safe_formula (Formula.Neg (\<phi>s ! n))
    then Regex.Test (Formula.Neg (Formula.Neg (Formula.Neg (\<phi>s ! n))))
    else Regex.Test (Formula.Neg (\<phi>s ! n)))"
| "from_mregex (MPlus r s) \<phi>s = Regex.Plus (from_mregex r \<phi>s) (from_mregex s \<phi>s)"
| "from_mregex (MTimes r s) \<phi>s = Regex.Times (from_mregex r \<phi>s) (from_mregex s \<phi>s)"
| "from_mregex (MStar r) \<phi>s = Regex.Star (from_mregex r \<phi>s)"

primrec to_mregex_exec where
  "to_mregex_exec (Regex.Skip n) xs = (MSkip n, xs)"
| "to_mregex_exec (Regex.Test \<phi>) xs = (if safe_formula \<phi> then (MTestPos (length xs), xs @ [\<phi>])
     else case \<phi> of Formula.Neg \<phi>' \<Rightarrow> (MTestNeg (length xs), xs @ [\<phi>']) | _ \<Rightarrow> (MSkip 0, xs))"
| "to_mregex_exec (Regex.Plus r s) xs =
     (let (mr, ys) = to_mregex_exec r xs; (ms, zs) = to_mregex_exec s ys
     in (MPlus mr ms, zs))"
| "to_mregex_exec (Regex.Times r s) xs =
     (let (mr, ys) = to_mregex_exec r xs; (ms, zs) = to_mregex_exec s ys
     in (MTimes mr ms, zs))"
| "to_mregex_exec (Regex.Star r) xs =
     (let (mr, ys) = to_mregex_exec r xs in (MStar mr, ys))"

primrec shift where
  "shift (MSkip n) k = MSkip n"
| "shift (MTestPos i) k = MTestPos (i + k)"
| "shift (MTestNeg i) k = MTestNeg (i + k)"
| "shift (MPlus r s) k = MPlus (shift r k) (shift s k)"
| "shift (MTimes r s) k = MTimes (shift r k) (shift s k)"
| "shift (MStar r) k = MStar (shift r k)"

primrec to_mregex where
  "to_mregex (Regex.Skip n) = (MSkip n, [])"
| "to_mregex (Regex.Test \<phi>) = (if safe_formula \<phi> then (MTestPos 0, [\<phi>])
     else case \<phi> of Formula.Neg \<phi>' \<Rightarrow> (MTestNeg 0, [\<phi>']) | _ \<Rightarrow> (MSkip 0, []))"
| "to_mregex (Regex.Plus r s) =
     (let (mr, ys) = to_mregex r; (ms, zs) = to_mregex s
     in (MPlus mr (shift ms (length ys)), ys @ zs))"
| "to_mregex (Regex.Times r s) =
     (let (mr, ys) = to_mregex r; (ms, zs) = to_mregex s
     in (MTimes mr (shift ms (length ys)), ys @ zs))"
| "to_mregex (Regex.Star r) =
     (let (mr, ys) = to_mregex r in (MStar mr, ys))"

lemma shift_0: "shift r 0 = r"
  by (induct r) auto

lemma shift_shift: "shift (shift r k) j = shift r (k + j)"
  by (induct r) auto

lemma to_mregex_to_mregex_exec:
  "case to_mregex r of (mr, \<phi>s) \<Rightarrow> to_mregex_exec r xs = (shift mr (length xs), xs @ \<phi>s)"
  by (induct r arbitrary: xs)
    (auto simp: shift_shift ac_simps split: formula.splits prod.splits)

lemma to_mregex_to_mregex_exec_Nil[code]: "to_mregex r = to_mregex_exec r []"
  using to_mregex_to_mregex_exec[where xs="[]" and r = r] by (auto simp: shift_0)

lemma ok_mono: "ok m mr \<Longrightarrow> m \<le> n \<Longrightarrow> ok n mr"
  by (induct mr) auto

lemma from_mregex_cong: "ok m mr \<Longrightarrow> (\<forall>i < m. xs ! i = ys ! i) \<Longrightarrow> from_mregex mr xs = from_mregex mr ys"
  by (induct mr) auto

lemma not_Neg_cases:
  "(\<forall>\<psi>. \<phi> \<noteq> Formula.Neg \<psi>) \<Longrightarrow> (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> x) = x"
  by (cases \<phi>) auto

lemma to_mregex_exec_ok:
  "to_mregex_exec r xs = (mr, ys) \<Longrightarrow> \<exists>zs. ys = xs @ zs \<and> set zs = atms r \<and> ok (length ys) mr"
proof (induct r arbitrary: xs mr ys)
  case (Skip x)
  then show ?case by (auto split: if_splits prod.splits simp: atms_def elim: ok_mono)
next
  case (Test x)
  show ?case proof (cases "\<exists>x'. x = Formula.Neg x'")
    case True
    with Test show ?thesis by (auto split: if_splits prod.splits simp: atms_def elim: ok_mono)
  next
    case False
    with Test show ?thesis by (auto split: if_splits prod.splits simp: atms_def not_Neg_cases elim: ok_mono)
  qed
next
  case (Plus r1 r2)
  then show ?case by (fastforce split: if_splits prod.splits formula.splits simp: atms_def elim: ok_mono)
next
  case (Times r1 r2)
  then show ?case by (fastforce split: if_splits prod.splits formula.splits simp: atms_def elim: ok_mono)
next
  case (Star r)
  then show ?case by (auto split: if_splits prod.splits simp: atms_def elim: ok_mono)
qed

lemma ok_shift: "ok (i + m) (Monitor.shift r i) \<longleftrightarrow> ok m r"
  by (induct r) auto

lemma to_mregex_ok: "to_mregex r = (mr, ys) \<Longrightarrow> set ys = atms r \<and> ok (length ys) mr"
proof (induct r arbitrary: mr ys)
  case (Skip x)
  then show ?case by (auto simp: atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Test x)
  show ?case proof (cases "\<exists>x'. x = Formula.Neg x'")
    case True
    with Test show ?thesis by (auto split: if_splits prod.splits simp: atms_def elim: ok_mono)
  next
    case False
    with Test show ?thesis by (auto split: if_splits prod.splits simp: atms_def not_Neg_cases elim: ok_mono)
  qed
next
  case (Plus r1 r2)
  then show ?case by (fastforce simp: ok_shift atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Times r1 r2)
  then show ?case by (fastforce simp: ok_shift atms_def elim: ok_mono split: if_splits prod.splits)
next
  case (Star r)
  then show ?case by (auto simp: atms_def elim: ok_mono split: if_splits prod.splits)
qed

lemma from_mregex_shift: "from_mregex (shift r (length xs)) (xs @ ys) = from_mregex r ys"
  by (induct r) (auto simp: nth_append)

lemma from_mregex_to_mregex: "safe_regex m g r \<Longrightarrow> case_prod from_mregex (to_mregex r) = r"
  by (induct r rule: safe_regex.induct)
    (auto dest: to_mregex_ok intro!: from_mregex_cong simp: nth_append from_mregex_shift cases_Neg_iff
      split: prod.splits modality.splits)

lemma from_mregex_eq: "safe_regex m g r \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow> from_mregex mr \<phi>s = r"
  using from_mregex_to_mregex[of m g r] by auto

lemma from_mregex_to_mregex_exec: "safe_regex m g r \<Longrightarrow> case_prod from_mregex (to_mregex_exec r xs) = r"
proof (induct r arbitrary: xs rule: safe_regex_induct)
  case (Plus b g r s)
  from Plus(3) Plus(1)[of xs] Plus(2)[of "snd (to_mregex_exec r xs)"] show ?case
    by (auto split: prod.splits simp: nth_append dest: to_mregex_exec_ok
        intro!: from_mregex_cong[where m = "length (snd (to_mregex_exec r xs))"])
next
  case (TimesF g r s)
  from TimesF(3) TimesF(2)[of xs] TimesF(1)[of "snd (to_mregex_exec r xs)"] show ?case
    by (auto split: prod.splits simp: nth_append dest: to_mregex_exec_ok
        intro!: from_mregex_cong[where m = "length (snd (to_mregex_exec r xs))"])
next
  case (TimesP g r s)
  from TimesP(3) TimesP(1)[of xs] TimesP(2)[of "snd (to_mregex_exec r xs)"] show ?case
    by (auto split: prod.splits simp: nth_append dest: to_mregex_exec_ok
        intro!: from_mregex_cong[where m = "length (snd (to_mregex_exec r xs))"])
next
  case (Star b g r)
  from Star(2) Star(1)[of xs] show ?case
    by (auto split: prod.splits)
qed (auto split: prod.splits simp: cases_Neg_iff)


derive linorder mregex

subsubsection \<open>LPD\<close>

definition saturate where
  "saturate f = while (\<lambda>S. f S \<noteq> S) f"

lemma saturate_code[code]:
  "saturate f S = (let S' = f S in if S' = S then S else saturate f S')"
  unfolding saturate_def Let_def
  by (subst while_unfold) auto

definition "MTimesL r S = MTimes r ` S"
definition "MTimesR R s = (\<lambda>r. MTimes r s) ` R"

primrec LPD where
  "LPD (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {MSkip m})"
| "LPD (MTestPos \<phi>) = {}"
| "LPD (MTestNeg \<phi>) = {}"
| "LPD (MPlus r s) = (LPD r \<union> LPD s)"
| "LPD (MTimes r s) = MTimesR (LPD r) s \<union> LPD s"
| "LPD (MStar r) = MTimesR (LPD r) (MStar r)"

primrec LPDi where
  "LPDi 0 r = {r}"
| "LPDi (Suc i) r = (\<Union>s \<in> LPD r. LPDi i s)"

lemma LPDi_Suc_alt: "LPDi (Suc i) r = (\<Union>s \<in> LPDi i r. LPD s)"
  by (induct i arbitrary: r) fastforce+

definition "LPDs r = (\<Union>i. LPDi i r)"

lemma LPDs_refl: "r \<in> LPDs r"
  by (auto simp: LPDs_def intro: exI[of _ 0])
lemma LPDs_trans: "r \<in> LPD s \<Longrightarrow> s \<in> LPDs t \<Longrightarrow> r \<in> LPDs t"
  by (force simp: LPDs_def LPDi_Suc_alt simp del: LPDi.simps intro: exI[of _ "Suc _"])

lemma LPDi_Test:
  "LPDi i (MSkip 0) \<subseteq> {MSkip 0}"
  "LPDi i (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "LPDi i (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  by (induct i) auto

lemma LPDs_Test:
  "LPDs (MSkip 0) \<subseteq> {MSkip 0}"
  "LPDs (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "LPDs (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  unfolding LPDs_def using LPDi_Test by blast+

lemma LPDi_MSkip: "LPDi i (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  by (induct i arbitrary: n) (auto dest: set_mp[OF LPDi_Test(1)] simp: le_Suc_eq split: nat.splits)

lemma LPDs_MSkip: "LPDs (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  unfolding LPDs_def using LPDi_MSkip by auto

lemma LPDi_Plus: "LPDi i (MPlus r s) \<subseteq> {MPlus r s} \<union> LPDi i r \<union> LPDi i s"
  by (induct i arbitrary: r s) auto

lemma LPDs_Plus: "LPDs (MPlus r s) \<subseteq> {MPlus r s} \<union> LPDs r \<union> LPDs s"
  unfolding LPDs_def using LPDi_Plus[of _ r s] by auto

lemma LPDi_Times:
  "LPDi i (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesR (\<Union>j \<le> i. LPDi j r) s \<union> (\<Union>j \<le> i. LPDi j s)"
proof (induct i arbitrary: r s)
  case (Suc i)
  show ?case
    by (fastforce simp: MTimesR_def dest: bspec[of _ _ "Suc _"] dest!: set_mp[OF Suc])
qed simp

lemma LPDs_Times: "LPDs (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesR (LPDs r) s \<union> LPDs s"
  unfolding LPDs_def using LPDi_Times[of _ r s] by (force simp: MTimesR_def)

lemma LPDi_Star: "j \<le> i \<Longrightarrow> LPDi j (MStar r) \<subseteq> {MStar r} \<union> MTimesR (\<Union>j \<le> i. LPDi j r) (MStar r)"
proof (induct i arbitrary: j r)
  case (Suc i)
  from Suc(2) show ?case
    by (auto 0 5 simp: MTimesR_def image_iff le_Suc_eq
        dest: bspec[of _ _ "Suc 0"] bspec[of _ _ "Suc _"] set_mp[OF Suc(1)] dest!: set_mp[OF LPDi_Times])
qed simp

lemma LPDs_Star: "LPDs (MStar r) \<subseteq> {MStar r} \<union> MTimesR (LPDs r) (MStar r)"
  unfolding LPDs_def using LPDi_Star[OF order_refl, of _ r] by (force simp: MTimesR_def)

lemma finite_LPDs: "finite (LPDs r)"
proof (induct r)
  case (MSkip n)
  then show ?case by (intro finite_subset[OF LPDs_MSkip]) simp
next
  case (MTestPos \<phi>)
  then show ?case by (intro finite_subset[OF LPDs_Test(2)]) simp
next
  case (MTestNeg \<phi>)
  then show ?case by (intro finite_subset[OF LPDs_Test(3)]) simp
next
  case (MPlus r s)
  then show ?case by (intro finite_subset[OF LPDs_Plus]) simp
next
  case (MTimes r s)
  then show ?case by (intro finite_subset[OF LPDs_Times]) (simp add: MTimesR_def)
next
  case (MStar r)
  then show ?case by (intro finite_subset[OF LPDs_Star]) (simp add: MTimesR_def)
qed

context begin

private abbreviation (input) "addLPD r \<equiv> \<lambda>S. insert r S \<union> Set.bind (insert r S) LPD"

private lemma mono_addLPD: "mono (addLPD r)"
  unfolding mono_def Set.bind_def by auto

private lemma LPDs_aux1: "lfp (addLPD r) \<subseteq> LPDs r"
  by (rule lfp_induct[OF mono_addLPD], auto intro: LPDs_refl LPDs_trans simp: Set.bind_def)

private lemma LPDs_aux2: "LPDi i r \<subseteq> lfp (addLPD r)"
proof (induct i)
  case 0
  then show ?case
    by (subst lfp_unfold[OF mono_addLPD]) auto
next
  case (Suc i)
  then show ?case
    by (subst lfp_unfold[OF mono_addLPD]) (auto simp: LPDi_Suc_alt simp del: LPDi.simps)
qed

lemma LPDs_alt: "LPDs r = lfp (addLPD r)"
  using LPDs_aux1 LPDs_aux2 by (force simp: LPDs_def)

lemma LPDs_code[code]:
  "LPDs r = saturate (addLPD r) {}"
  unfolding LPDs_alt saturate_def
  by (rule lfp_while[OF mono_addLPD _ finite_LPDs, of r]) (auto simp: LPDs_refl LPDs_trans Set.bind_def)

end

subsubsection \<open>RPD\<close>

primrec RPD where
  "RPD (MSkip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {MSkip m})"
| "RPD (MTestPos \<phi>) = {}"
| "RPD (MTestNeg \<phi>) = {}"
| "RPD (MPlus r s) = (RPD r \<union> RPD s)"
| "RPD (MTimes r s) = MTimesL r (RPD s) \<union> RPD r"
| "RPD (MStar r) = MTimesL (MStar r) (RPD r)"

primrec RPDi where
  "RPDi 0 r = {r}"
| "RPDi (Suc i) r = (\<Union>s \<in> RPD r. RPDi i s)"

lemma RPDi_Suc_alt: "RPDi (Suc i) r = (\<Union>s \<in> RPDi i r. RPD s)"
  by (induct i arbitrary: r) fastforce+

definition "RPDs r = (\<Union>i. RPDi i r)"

lemma RPDs_refl: "r \<in> RPDs r"
  by (auto simp: RPDs_def intro: exI[of _ 0])
lemma RPDs_trans: "r \<in> RPD s \<Longrightarrow> s \<in> RPDs t \<Longrightarrow> r \<in> RPDs t"
  by (force simp: RPDs_def RPDi_Suc_alt simp del: RPDi.simps intro: exI[of _ "Suc _"])

lemma RPDi_Test:
  "RPDi i (MSkip 0) \<subseteq> {MSkip 0}"
  "RPDi i (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "RPDi i (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  by (induct i) auto

lemma RPDs_Test:
  "RPDs (MSkip 0) \<subseteq> {MSkip 0}"
  "RPDs (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "RPDs (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  unfolding RPDs_def using RPDi_Test by blast+

lemma RPDi_MSkip: "RPDi i (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  by (induct i arbitrary: n) (auto dest: set_mp[OF RPDi_Test(1)] simp: le_Suc_eq split: nat.splits)

lemma RPDs_MSkip: "RPDs (MSkip n) \<subseteq> MSkip ` {i. i \<le> n}"
  unfolding RPDs_def using RPDi_MSkip by auto

lemma RPDi_Plus: "RPDi i (MPlus r s) \<subseteq> {MPlus r s} \<union> RPDi i r \<union> RPDi i s"
  by (induct i arbitrary: r s) auto

lemma RPDi_Suc_RPD_Plus:
  "RPDi (Suc i) r \<subseteq> RPDs (MPlus r s)"
  "RPDi (Suc i) s \<subseteq> RPDs (MPlus r s)"
  unfolding RPDs_def by (force intro!: exI[of _ "Suc i"])+

lemma RPDs_Plus: "RPDs (MPlus r s) \<subseteq> {MPlus r s} \<union> RPDs r \<union> RPDs s"
  unfolding RPDs_def using RPDi_Plus[of _ r s] by auto

lemma RPDi_Times:
  "RPDi i (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesL r (\<Union>j \<le> i. RPDi j s) \<union> (\<Union>j \<le> i. RPDi j r)"
proof (induct i arbitrary: r s)
  case (Suc i)
  show ?case
    by (fastforce simp: MTimesL_def dest: bspec[of _ _ "Suc _"] dest!: set_mp[OF Suc])
qed simp

lemma RPDs_Times: "RPDs (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesL r (RPDs s) \<union> RPDs r"
  unfolding RPDs_def using RPDi_Times[of _ r s] by (force simp: MTimesL_def)

lemma RPDi_Star: "j \<le> i \<Longrightarrow> RPDi j (MStar r) \<subseteq> {MStar r} \<union> MTimesL (MStar r) (\<Union>j \<le> i. RPDi j r)"
proof (induct i arbitrary: j r)
  case (Suc i)
  from Suc(2) show ?case
    by (auto 0 5 simp: MTimesL_def image_iff le_Suc_eq
        dest: bspec[of _ _ "Suc 0"] bspec[of _ _ "Suc _"] set_mp[OF Suc(1)] dest!: set_mp[OF RPDi_Times])
qed simp

lemma RPDs_Star: "RPDs (MStar r) \<subseteq> {MStar r} \<union> MTimesL (MStar r) (RPDs r)"
  unfolding RPDs_def using RPDi_Star[OF order_refl, of _ r] by (force simp: MTimesL_def)

lemma finite_RPDs: "finite (RPDs r)"
proof (induct r)
  case MSkip
  then show ?case by (intro finite_subset[OF RPDs_MSkip]) simp
next
  case (MTestPos \<phi>)
  then show ?case by (intro finite_subset[OF RPDs_Test(2)]) simp
next
  case (MTestNeg \<phi>)
  then show ?case by (intro finite_subset[OF RPDs_Test(3)]) simp
next
  case (MPlus r s)
  then show ?case by (intro finite_subset[OF RPDs_Plus]) simp
next
  case (MTimes r s)
  then show ?case by (intro finite_subset[OF RPDs_Times]) (simp add: MTimesL_def)
next
  case (MStar r)
  then show ?case by (intro finite_subset[OF RPDs_Star]) (simp add: MTimesL_def)
qed

context begin

private abbreviation (input) "addRPD r \<equiv> \<lambda>S. insert r S \<union> Set.bind (insert r S) RPD"

private lemma mono_addRPD: "mono (addRPD r)"
  unfolding mono_def Set.bind_def by auto

private lemma RPDs_aux1: "lfp (addRPD r) \<subseteq> RPDs r"
  by (rule lfp_induct[OF mono_addRPD], auto intro: RPDs_refl RPDs_trans simp: Set.bind_def)

private lemma RPDs_aux2: "RPDi i r \<subseteq> lfp (addRPD r)"
proof (induct i)
  case 0
  then show ?case
    by (subst lfp_unfold[OF mono_addRPD]) auto
next
  case (Suc i)
  then show ?case
    by (subst lfp_unfold[OF mono_addRPD]) (auto simp: RPDi_Suc_alt simp del: RPDi.simps)
qed

lemma RPDs_alt: "RPDs r = lfp (addRPD r)"
  using RPDs_aux1 RPDs_aux2 by (force simp: RPDs_def)

lemma RPDs_code[code]:
  "RPDs r = saturate (addRPD r) {}"
  unfolding RPDs_alt saturate_def
  by (rule lfp_while[OF mono_addRPD _ finite_RPDs, of r]) (auto simp: RPDs_refl RPDs_trans Set.bind_def)

end

subsection \<open>The executable monitor\<close>

type_synonym ts = nat

type_synonym 'a mbuf2 = "('a table) list \<times> ('a table) list"
type_synonym 'a mbuft2 = "('a table) list \<times> (nat set \<times> 'a table) list"
type_synonym 'a mbufn = "('a table) list list"
type_synonym 'a msaux = "(ts \<times> 'a table) list"
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"
type_synonym 'a muaux = "(ts \<times> 'a table \<times> 'a table) list"
type_synonym 'a mr\<delta>aux = "(ts \<times> (mregex, 'a table) mapping) list"
type_synonym 'a ml\<delta>aux = "(ts \<times> 'a table list \<times> 'a table) list"

datatype mconstraint = MEq | MLess | MLessEq

record args =
  args_ivl :: \<I>
  args_n :: nat
  args_L :: "nat set"
  args_R :: "nat set"
  args_pos :: bool

datatype (dead 'msaux, dead 'muaux, dead 'mtaux) mformula =
  MRel "event_data table"
  | MPred Formula.name "Formula.trm list"
  | MLet Formula.name nat "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula"
  | MAnd "nat set" "('msaux, 'muaux, 'mtaux) mformula" bool "nat set" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2"
  | MAndAssign "('msaux, 'muaux, 'mtaux) mformula" "nat \<times> Formula.trm"
  | MAndRel "('msaux, 'muaux, 'mtaux) mformula" "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | MAndTrigger "nat set" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuft2" args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" "'mtaux"
  | MAnds "nat set list" "nat set list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn"
  | MOr "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2"
  | MNeg "('msaux, 'muaux, 'mtaux) mformula"
  | MExists "('msaux, 'muaux, 'mtaux) mformula"
  | MAgg bool nat Formula.agg_op nat "Formula.trm" "('msaux, 'muaux, 'mtaux) mformula"
  | MPrev \<I> "('msaux, 'muaux, 'mtaux) mformula" bool "event_data table list" "ts list"
  | MNext \<I> "('msaux, 'muaux, 'mtaux) mformula" bool "ts list"
  | MSince args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" "'msaux"
  | MUntil args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" ts "'muaux"
  | MTrigger args "('msaux, 'muaux, 'mtaux) mformula" "('msaux, 'muaux, 'mtaux) mformula" "event_data mbuf2" "ts list" "'mtaux"
  | MMatchP \<I> "mregex" "mregex list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn" "ts list" "event_data mr\<delta>aux"
  | MMatchF \<I> "mregex" "mregex list" "('msaux, 'muaux, 'mtaux) mformula list" "event_data mbufn" "ts list" ts "event_data ml\<delta>aux"

record ('msaux, 'muaux, 'mtaux) mstate =
  mstate_i :: nat
  mstate_m :: "('msaux, 'muaux, 'mtaux) mformula"
  mstate_n :: nat

fun eq_rel :: "nat \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm \<Rightarrow> event_data table" where
  "eq_rel n (Formula.Const x) (Formula.Const y) = (if x = y then unit_table n else empty_table)"
| "eq_rel n (Formula.Var x) (Formula.Const y) = singleton_table n x y"
| "eq_rel n (Formula.Const x) (Formula.Var y) = singleton_table n y x"
| "eq_rel n _ _ = undefined"

lemma regex_atms_size: "x \<in> regex.atms r \<Longrightarrow> size x < regex.size_regex size r"
  by (induct r) auto

lemma regex_atms_size': "x \<in> regex.atms r \<Longrightarrow> size' x < regex.size_regex size' r"
  by (induct r) auto

lemma atms_size:
  assumes "x \<in> atms r"
  shows "size x < Regex.size_regex size r"
proof -
  { fix y assume "y \<in> regex.atms r" "case y of formula.Neg z \<Rightarrow> x = z | _ \<Rightarrow> False"
    then have "size x < Regex.size_regex size r"
      by (cases y rule: formula.exhaust) (auto dest: regex_atms_size)
  }
  with assms show ?thesis
    unfolding atms_def
    by (auto split: formula.splits dest: regex_atms_size)
qed

lemma atms_size':
  assumes "x \<in> atms r"
  shows "size' x < Regex.size_regex size' r"
proof -
  { fix y assume "y \<in> regex.atms r" "case y of formula.Neg z \<Rightarrow> x = z | _ \<Rightarrow> False"
    then have "size' x < Regex.size_regex size' r"
      by (cases y rule: formula.exhaust) (auto dest: regex_atms_size')
  }
  with assms show ?thesis
    unfolding atms_def
    by (auto split: formula.splits dest: regex_atms_size')
qed

definition init_args :: "\<I> \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> bool \<Rightarrow> args" where
  "init_args I n L R pos = \<lparr>args_ivl = I, args_n = n, args_L = L, args_R = R, args_pos = pos\<rparr>"

locale msaux =
  fixes valid_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> event_data msaux \<Rightarrow> bool"
    and init_msaux :: "args \<Rightarrow> 'msaux"
    and add_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and add_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and result_msaux :: "args \<Rightarrow> 'msaux \<Rightarrow> event_data table"
  assumes valid_init_msaux: "L \<subseteq> R \<Longrightarrow>
    valid_msaux (init_args I n L R pos) 0 (init_msaux (init_args I n L R pos)) []"
  assumes valid_add_new_ts_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    valid_msaux args nt (add_new_ts_msaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  assumes valid_join_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow>
    table (args_n args) (args_L args) rel1 \<Longrightarrow>
    valid_msaux args cur (join_msaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
  assumes valid_add_new_table_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow>
    table (args_n args) (args_R args) rel2 \<Longrightarrow>
    valid_msaux args cur (add_new_table_msaux args rel2 aux)
    (case auxlist of
      [] => [(cur, rel2)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
    and valid_result_msaux: "valid_msaux args cur aux auxlist \<Longrightarrow> result_msaux args aux =
    foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"

fun trigger_results :: "args \<Rightarrow> ts \<Rightarrow> event_data mtaux \<Rightarrow> (nat set \<times> event_data table)" where
  "trigger_results args cur auxlist = (
    if (length (filter (\<lambda> (t, _, _). mem (args_ivl args) (cur - t)) auxlist) > 0) then (
      (args_R args), {
      tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
        \<comment> \<open>pretty much the definition of trigger\<close>
        (\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (cur - t) \<longrightarrow> 
          \<comment> \<open>either \<psi> holds or there is a later database where the same tuple satisfies \<phi>\<close>
          (
            tuple \<in> r \<or>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) ((fst o snd) (auxlist!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple) \<comment> \<open>t < t' is given as the list is sorted\<close>
            )
          )
        )
      }
    ) else
    ({}, {replicate (args_n args) None})
)"

locale mtaux =
  fixes valid_mtaux :: "args \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool"
    and init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    (* and update_mtaux_constraint :: "args \<Rightarrow> ts \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux" *)
    (* and update_mtaux_safe_assignment :: "args \<Rightarrow> ts \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux" *)
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> (nat set \<times> event_data table)"

  (* the initial state should be valid *)
  assumes valid_init_mtaux: "(
    if (mem I 0)
      then
        L \<subseteq> R
      else 
        L = R
    ) \<Longrightarrow>
    \<not>mem I 0 \<longrightarrow> pos \<Longrightarrow>
    let args = init_args I n L R pos in
    valid_mtaux args 0 (init_mtaux args) []"

  (* assuming the previous state outputted the same result, the next will as well *)
  assumes valid_update_mtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (args_n args) (args_L args) l \<Longrightarrow>
    table (args_n args) (args_R args) r \<Longrightarrow>
    valid_mtaux args cur aux auxlist \<Longrightarrow>
    valid_mtaux
      args
      nt
      (update_mtaux args nt l r aux)
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "

  and valid_result_mtaux: "
    valid_mtaux args cur aux auxlist \<Longrightarrow>
    result_mtaux args aux = trigger_results args cur auxlist
  "

fun check_before :: "\<I> \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a \<times> 'b) \<Rightarrow> bool" where
  "check_before I dt (t, a, b) \<longleftrightarrow> \<not> memR I (dt - t)"

fun proj_thd :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'c" where
  "proj_thd (t, a1, a2) = a2"

definition update_until :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow> event_data muaux" where
  "update_until args rel1 rel2 nt aux =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if (args_pos args) then join a1 True rel1 else a1 \<union> rel1,
      if mem  (args_ivl args) (nt - t) then a2 \<union> join rel2 (args_pos args) a1 else a2)) aux) @
    [(nt, rel1, if memL (args_ivl args) 0 then rel2 else empty_table)]"

lemma map_proj_thd_update_until: "map proj_thd (takeWhile (check_before (args_ivl args) nt) auxlist) =
  map proj_thd (takeWhile (check_before (args_ivl args) nt) (update_until args rel1 rel2 nt auxlist))"
proof (induction auxlist)
  case Nil
  then show ?case by (simp add: update_until_def)
next
  case (Cons a auxlist)
  then show ?case
    by (auto simp add: update_until_def split: if_splits prod.splits)
qed

fun eval_until :: "\<I> \<Rightarrow> ts \<Rightarrow> event_data muaux \<Rightarrow> event_data table list \<times> event_data muaux" where
  "eval_until I nt [] = ([], [])"
| "eval_until I nt ((t, a1, a2) # aux) = (if \<not> memR I (nt - t) then
    (let (xs, aux) = eval_until I nt aux in (a2 # xs, aux)) else ([], (t, a1, a2) # aux))"

lemma eval_until_length:
  "eval_until I nt auxlist = (res, auxlist') \<Longrightarrow> length auxlist = length res + length auxlist'"
  by (induction I nt auxlist arbitrary: res auxlist' rule: eval_until.induct)
    (auto split: if_splits prod.splits)

lemma eval_until_res: "eval_until I nt auxlist = (res, auxlist') \<Longrightarrow>
  res = map proj_thd (takeWhile (check_before I nt) auxlist)"
  by (induction I nt auxlist arbitrary: res auxlist' rule: eval_until.induct)
    (auto split: prod.splits)

lemma eval_until_auxlist': "eval_until I nt auxlist = (res, auxlist') \<Longrightarrow>
  auxlist' = drop (length res) auxlist"
  by (induction I nt auxlist arbitrary: res auxlist' rule: eval_until.induct)
    (auto split: if_splits prod.splits)

locale muaux =
  fixes valid_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data muaux \<Rightarrow> bool"
    and init_muaux :: "args \<Rightarrow> 'muaux"
    and add_new_muaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> 'muaux"
    and length_muaux :: "args \<Rightarrow> 'muaux \<Rightarrow> nat"
    and eval_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data table list \<times> 'muaux"
  assumes valid_init_muaux: "L \<subseteq> R \<Longrightarrow>
    valid_muaux (init_args I n L R pos) 0 (init_muaux (init_args I n L R pos)) []"
  assumes valid_add_new_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow>
    table (args_n args) (args_L args) rel1 \<Longrightarrow>
    table (args_n args) (args_R args) rel2 \<Longrightarrow>
    nt \<ge> cur \<Longrightarrow>
    valid_muaux args nt (add_new_muaux args rel1 rel2 nt aux)
    (update_until args rel1 rel2 nt auxlist)"
  assumes valid_length_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow> length_muaux args aux = length auxlist"
  assumes valid_eval_muaux: "valid_muaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
    eval_muaux args nt aux = (res, aux') \<Longrightarrow> eval_until (args_ivl args) nt auxlist = (res', auxlist') \<Longrightarrow>
    res = res' \<and> valid_muaux args cur aux' auxlist'"

locale maux = msaux valid_msaux init_msaux add_new_ts_msaux join_msaux add_new_table_msaux result_msaux +
  muaux valid_muaux init_muaux add_new_muaux length_muaux eval_muaux + 
  mtaux valid_mtaux init_mtaux update_mtaux result_mtaux
  for valid_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> event_data msaux \<Rightarrow> bool"
    and init_msaux :: "args \<Rightarrow> 'msaux"
    and add_new_ts_msaux :: "args \<Rightarrow> ts \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and join_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and add_new_table_msaux :: "args \<Rightarrow> event_data table \<Rightarrow> 'msaux \<Rightarrow> 'msaux"
    and result_msaux :: "args \<Rightarrow> 'msaux \<Rightarrow> event_data table"

    and valid_muaux :: "args \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> event_data muaux \<Rightarrow> bool"
    and init_muaux :: "args \<Rightarrow> 'muaux"
    and add_new_muaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'muaux \<Rightarrow> 'muaux"
    and length_muaux :: "args \<Rightarrow> 'muaux \<Rightarrow> nat"
    and eval_muaux :: "args \<Rightarrow> nat \<Rightarrow> 'muaux \<Rightarrow> event_data table list \<times> 'muaux"

    and valid_mtaux :: "args \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool"
    and init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> (nat set \<times> event_data table)"

fun split_assignment :: "nat set \<Rightarrow> Formula.formula \<Rightarrow> nat \<times> Formula.trm" where
  "split_assignment X (Formula.Eq t1 t2) = (case (t1, t2) of
      (Formula.Var x, Formula.Var y) \<Rightarrow> if x \<in> X then (y, t1) else (x, t2)
    | (Formula.Var x, _) \<Rightarrow> (x, t2)
    | (_, Formula.Var y) \<Rightarrow> (y, t1))"
| "split_assignment _ _ = undefined"

fun split_constraint :: "Formula.formula \<Rightarrow> Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm" where
  "split_constraint (Formula.Eq t1 t2) = (t1, True, MEq, t2)"
| "split_constraint (Formula.Less t1 t2) = (t1, True, MLess, t2)"
| "split_constraint (Formula.LessEq t1 t2) = (t1, True, MLessEq, t2)"
| "split_constraint (Formula.Neg (Formula.Eq t1 t2)) = (t1, False, MEq, t2)"
| "split_constraint (Formula.Neg (Formula.Less t1 t2)) = (t1, False, MLess, t2)"
| "split_constraint (Formula.Neg (Formula.LessEq t1 t2)) = (t1, False, MLessEq, t2)"
| "split_constraint _ = undefined"

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

lemma size'_remove_neg[termination_simp]: "size' (remove_neg \<phi>) \<le> size' \<phi>"
  by (cases \<phi>) simp_all

lemma fv_remove_neg: "fv \<phi> = fv (remove_neg \<phi>)"
  by (cases \<phi>) auto

function (in maux) (sequential) minit0 :: "nat \<Rightarrow> Formula.formula \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula" where
  "minit0 n (Formula.Neg \<phi>) = (let V = fv \<phi> in (if V = {} then MNeg (minit0 n \<phi>) else MRel empty_table))"
| "minit0 n (Formula.Eq t1 t2) = MRel (eq_rel n t1 t2)"
| "minit0 n (Formula.Pred e ts) = MPred e ts"
| "minit0 n (Formula.Let p \<phi> \<psi>) = MLet p (Formula.nfv \<phi>) (minit0 (Formula.nfv \<phi>) \<phi>) (minit0 n \<psi>)"
| "minit0 n (Formula.Or \<phi> \<psi>) = MOr (minit0 n \<phi>) (minit0 n \<psi>) ([], [])"
| "minit0 n (Formula.And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      MAndAssign (minit0 n \<phi>) (split_assignment (fv \<phi>) \<psi>)
    else if safe_formula \<psi> then
      MAnd (fv \<phi>) (minit0 n \<phi>) True (fv \<psi>) (minit0 n \<psi>) ([], [])
    else if is_constraint \<psi> then
      MAndRel (minit0 n \<phi>) (split_constraint \<psi>)
    else (case \<psi> of
        (Formula.Neg \<psi>) \<Rightarrow> MAnd (fv \<phi>) (minit0 n \<phi>) False (fv \<psi>) (minit0 n \<psi>) ([], [])
      | (Formula.Trigger \<phi>' I \<psi>') \<Rightarrow> (
          if (safe_formula \<phi>') then
            MAndTrigger (fv \<phi>) (minit0 n \<phi>) ([], []) (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') True) (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mtaux (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') True))
          else (case \<phi>' of (Formula.Neg \<phi>') \<Rightarrow>
            MAndTrigger (fv \<phi>) (minit0 n \<phi>) ([], []) (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') False) (minit0 n \<phi>') (minit0 n \<psi>') ([], []) [] (init_mtaux (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') False))
          )
        )
      | (Formula.Release \<phi>' I \<psi>') \<Rightarrow> minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
      )
)"
| "minit0 n (Formula.Ands l) = (let (pos, neg) = partition safe_formula l in
    let mpos = map (minit0 n) pos in
    let mneg = map (minit0 n) (map remove_neg neg) in \<comment> \<open>Trigger is passed as is\<close>
    let vpos = map fv pos in
    let vneg = map fv neg in
    MAnds vpos vneg (mpos @ mneg) (replicate (length l) []))"
| "minit0 n (Formula.Exists \<phi>) = MExists (minit0 (Suc n) \<phi>)"
| "minit0 n (Formula.Agg y \<omega> b f \<phi>) = MAgg (fv \<phi> \<subseteq> {0..<b}) y \<omega> b f (minit0 (b + n) \<phi>)"
| "minit0 n (Formula.Prev I \<phi>) = MPrev I (minit0 n \<phi>) True [] []"
| "minit0 n (Formula.Next I \<phi>) = MNext I (minit0 n \<phi>) True []"
| "minit0 n (Formula.Since \<phi> I \<psi>) = (if safe_formula \<phi>
    then MSince (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_msaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True))
    else (case \<phi> of
      Formula.Neg \<phi> \<Rightarrow> MSince (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_msaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False))
    | _ \<Rightarrow> undefined))"
| "minit0 n (Formula.Until \<phi> I \<psi>) = (if safe_formula \<phi>
    then MUntil (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True))
    else (case \<phi> of
      Formula.Neg \<phi> \<Rightarrow> MUntil (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] 0 (init_muaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False))
    | _ \<Rightarrow> undefined))"
| "minit0 n (Formula.Trigger \<phi> I \<psi>) = (if safe_formula \<phi>
    then MTrigger (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mtaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True))
    else (case \<phi> of
      Formula.Neg \<phi> \<Rightarrow> MTrigger (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False) (minit0 n \<phi>) (minit0 n \<psi>) ([], []) [] (init_mtaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False))
    | _ \<Rightarrow> undefined))
"
| "minit0 n (Formula.Release \<phi> I \<psi>) = (
  if mem I 0
    then
      minit0 n (release_safe_0 \<phi> I \<psi>)
    else
      minit0 n (release_safe_bounded \<phi> I \<psi>)
  )
"
| "minit0 n (Formula.MatchP I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchP I mr (sorted_list_of_set (RPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] [])"
| "minit0 n (Formula.MatchF I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchF I mr (sorted_list_of_set (LPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] 0 [])"
| "minit0 n _ = undefined"
  by pat_completeness auto
termination (in maux)
  apply (relation "measure (\<lambda>(_, \<phi>). size' \<phi>)")
  apply (auto simp: less_Suc_eq_le size_list_estimation' dest!: to_mregex_ok[OF sym] atms_size')
  using size'_and_release size'_Release size'_Or size'_release_aux
  apply (auto dest!: sum_list_mem_leq[of _ _ size'])
  using size'_remove_neg le_trans
  by metis
  

context maux begin
declare minit0.simps(15) [simp del]
end

lemma safe_assignment_next: "\<not>safe_assignment (fv \<psi>) (formula.Next I \<phi>)"
  unfolding safe_assignment_def
  by auto

lemma constraint_eventually: "\<not>is_constraint (formula.Neg (Formula.eventually I \<phi>))"
  unfolding eventually_def
  by auto

lemma (in maux) minit0_release_0:
  assumes mem: "mem I 0"
  shows "minit0 n (Formula.Release \<phi> I \<psi>) = minit0 n (release_safe_0 \<phi> I \<psi>)"
  using assms
  by (auto simp add: minit0.simps(15))

lemma (in maux) minit0_release_bounded:
  assumes mem: "\<not>mem I 0"
  shows "minit0 n (Formula.Release \<phi> I \<psi>) = minit0 n (release_safe_bounded \<phi> I \<psi>)"
  using assms
  by (auto simp add: minit0.simps(15))

definition (in maux) minit :: "Formula.formula \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate" where
  "minit \<phi> = (let n = Formula.nfv \<phi> in \<lparr>mstate_i = 0, mstate_m = minit0 n \<phi>, mstate_n = n\<rparr>)"

definition (in maux) minit_safe where
  "minit_safe \<phi> = (if mmonitorable_exec \<phi> then minit \<phi> else undefined)"

fun mprev_next :: "\<I> \<Rightarrow> (event_data table) list \<Rightarrow> ts list \<Rightarrow> (event_data table) list \<times> (event_data table) list \<times> ts list" where
  "mprev_next I [] ts = ([], [], ts)"
| "mprev_next I xs [] = ([], xs, [])"
| "mprev_next I xs [t] = ([], xs, [t])"
| "mprev_next I (x # xs) (t # t' # ts) = (let (ys, zs) = mprev_next I xs (t' # ts)
    in ((if mem I ((t' - t)) then x else (empty_table)) # ys, zs))"

fun mbuf2_add where
  "mbuf2_add xs' ys' (xs, ys) = (xs @ xs', ys @ ys')"

fun mbuf2_take where
  "mbuf2_take f (x # xs, y # ys) = (let (zs, buf) = mbuf2_take f (xs, ys) in (f x y # zs, buf))"
| "mbuf2_take f (xs, ys) = ([], (xs, ys))"

fun mbuf2t_take where
  "mbuf2t_take f z (x # xs, y # ys) (t # ts) = mbuf2t_take f (f x y t z) (xs, ys) ts"
| "mbuf2t_take f z (xs, ys) ts = (z, (xs, ys), ts)"

lemma size_list_length_diff1: "xs \<noteq> [] \<Longrightarrow> [] \<notin> set xs \<Longrightarrow>
  size_list (\<lambda>xs. length xs - Suc 0) xs < size_list length xs"
proof (induct xs)
  case (Cons x xs)
  then show ?case
    by (cases xs) auto
qed simp

fun mbufn_add :: "(event_data table) list list \<Rightarrow> event_data mbufn \<Rightarrow> event_data mbufn" where
  "mbufn_add xs' xs = List.map2 (@) xs xs'"

function mbufn_take :: "((event_data table) list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> event_data mbufn \<Rightarrow> 'b \<times> event_data mbufn" where
  "mbufn_take f z buf = (if buf = [] \<or> [] \<in> set buf then (z, buf)
    else mbufn_take f (f (map hd buf) z) (map tl buf))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(_, _, buf). size_list length buf)")
    (auto simp: comp_def Suc_le_eq size_list_length_diff1)

fun mbufnt_take :: "((event_data table) list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> event_data mbufn \<Rightarrow> ts list \<Rightarrow> 'b \<times> event_data mbufn \<times> ts list" where
  "mbufnt_take f z buf ts =
    (if [] \<in> set buf \<or> ts = [] then (z, buf, ts)
    else mbufnt_take f (f (map hd buf) (hd ts) z) (map tl buf) (tl ts))"

fun match :: "Formula.trm list \<Rightarrow> event_data list \<Rightarrow> (nat \<rightharpoonup> event_data) option" where
  "match [] [] = Some Map.empty"
| "match (Formula.Const x # ts) (y # ys) = (if x = y then match ts ys else None)"
| "match (Formula.Var x # ts) (y # ys) = (case match ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "match _ _ = None"

fun meval_trm :: "Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> event_data" where
  "meval_trm (Formula.Var x) v = the (v ! x)"
| "meval_trm (Formula.Const x) v = x"
| "meval_trm (Formula.Plus x y) v = meval_trm x v + meval_trm y v"
| "meval_trm (Formula.Minus x y) v = meval_trm x v - meval_trm y v"
| "meval_trm (Formula.UMinus x) v = - meval_trm x v"
| "meval_trm (Formula.Mult x y) v = meval_trm x v * meval_trm y v"
| "meval_trm (Formula.Div x y) v = meval_trm x v div meval_trm y v"
| "meval_trm (Formula.Mod x y) v = meval_trm x v mod meval_trm y v"
| "meval_trm (Formula.F2i x) v = EInt (integer_of_event_data (meval_trm x v))"
| "meval_trm (Formula.I2f x) v = EFloat (double_of_event_data (meval_trm x v))"

definition eval_agg :: "nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> Formula.agg_op \<Rightarrow> nat \<Rightarrow> Formula.trm \<Rightarrow>
  event_data table \<Rightarrow> event_data table" where
  "eval_agg n g0 y \<omega> b f rel = (if g0 \<and> rel = empty_table
    then singleton_table n y (eval_agg_op \<omega> {})
    else (\<lambda>k.
      let group = Set.filter (\<lambda>x. drop b x = k) rel;
        M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
      in k[y:=Some (eval_agg_op \<omega> M)]) ` (drop b) ` rel)"

definition (in maux) update_since :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow>
  'msaux \<Rightarrow> event_data table \<times> 'msaux" where
  "update_since args rel1 rel2 nt aux =
    (let aux0 = join_msaux args rel1 (add_new_ts_msaux args nt aux);
         aux' = add_new_table_msaux args rel2 aux0
    in (result_msaux args aux', aux'))"

definition "lookup = Mapping.lookup_default empty_table"

fun \<epsilon>_lax where
  "\<epsilon>_lax guard \<phi>s (MSkip n) = (if n = 0 then guard else empty_table)"
| "\<epsilon>_lax guard \<phi>s (MTestPos i) = join guard True (\<phi>s ! i)"
| "\<epsilon>_lax guard \<phi>s (MTestNeg i) = join guard False (\<phi>s ! i)"
| "\<epsilon>_lax guard \<phi>s (MPlus r s) = \<epsilon>_lax guard \<phi>s r \<union> \<epsilon>_lax guard \<phi>s s"
| "\<epsilon>_lax guard \<phi>s (MTimes r s) = join (\<epsilon>_lax guard \<phi>s r) True (\<epsilon>_lax guard \<phi>s s)"
| "\<epsilon>_lax guard \<phi>s (MStar r) = guard"

fun r\<epsilon>_strict where
  "r\<epsilon>_strict n \<phi>s (MSkip m) = (if m = 0 then unit_table n else empty_table)"
| "r\<epsilon>_strict n \<phi>s (MTestPos i) = \<phi>s ! i"
| "r\<epsilon>_strict n \<phi>s (MTestNeg i) = (if \<phi>s ! i = empty_table then unit_table n else empty_table)"
| "r\<epsilon>_strict n \<phi>s (MPlus r s) = r\<epsilon>_strict n \<phi>s r \<union> r\<epsilon>_strict n \<phi>s s"
| "r\<epsilon>_strict n \<phi>s (MTimes r s) = \<epsilon>_lax (r\<epsilon>_strict n \<phi>s r) \<phi>s s"
| "r\<epsilon>_strict n \<phi>s (MStar r) = unit_table n"

fun l\<epsilon>_strict where
  "l\<epsilon>_strict n \<phi>s (MSkip m) = (if m = 0 then unit_table n else empty_table)"
| "l\<epsilon>_strict n \<phi>s (MTestPos i) = \<phi>s ! i"
| "l\<epsilon>_strict n \<phi>s (MTestNeg i) = (if \<phi>s ! i = empty_table then unit_table n else empty_table)"
| "l\<epsilon>_strict n \<phi>s (MPlus r s) = l\<epsilon>_strict n \<phi>s r \<union> l\<epsilon>_strict n \<phi>s s"
| "l\<epsilon>_strict n \<phi>s (MTimes r s) = \<epsilon>_lax (l\<epsilon>_strict n \<phi>s s) \<phi>s r"
| "l\<epsilon>_strict n \<phi>s (MStar r) = unit_table n"

fun r\<delta> :: "(mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> 'a table list \<Rightarrow> mregex \<Rightarrow> 'a table"  where
  "r\<delta> \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> empty_table | Suc m \<Rightarrow> lookup X (\<kappa> (MSkip m)))"
| "r\<delta> \<kappa> X \<phi>s (MTestPos i) = empty_table"
| "r\<delta> \<kappa> X \<phi>s (MTestNeg i) = empty_table"
| "r\<delta> \<kappa> X \<phi>s (MPlus r s) = r\<delta> \<kappa> X \<phi>s r \<union> r\<delta> \<kappa> X \<phi>s s"
| "r\<delta> \<kappa> X \<phi>s (MTimes r s) = r\<delta> (\<lambda>t. \<kappa> (MTimes r t)) X \<phi>s s \<union> \<epsilon>_lax (r\<delta> \<kappa> X \<phi>s r) \<phi>s s"
| "r\<delta> \<kappa> X \<phi>s (MStar r) = r\<delta> (\<lambda>t. \<kappa> (MTimes (MStar r) t)) X \<phi>s r"

fun l\<delta> :: "(mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> 'a table list \<Rightarrow> mregex \<Rightarrow> 'a table" where
  "l\<delta> \<kappa> X \<phi>s (MSkip n) = (case n of 0 \<Rightarrow> empty_table | Suc m \<Rightarrow> lookup X (\<kappa> (MSkip m)))"
| "l\<delta> \<kappa> X \<phi>s (MTestPos i) = empty_table"
| "l\<delta> \<kappa> X \<phi>s (MTestNeg i) = empty_table"
| "l\<delta> \<kappa> X \<phi>s (MPlus r s) = l\<delta> \<kappa> X \<phi>s r \<union> l\<delta> \<kappa> X \<phi>s s"
| "l\<delta> \<kappa> X \<phi>s (MTimes r s) = l\<delta> (\<lambda>t. \<kappa> (MTimes t s)) X \<phi>s r \<union> \<epsilon>_lax (l\<delta> \<kappa> X \<phi>s s) \<phi>s r"
| "l\<delta> \<kappa> X \<phi>s (MStar r) = l\<delta> (\<lambda>t. \<kappa> (MTimes t (MStar r))) X \<phi>s r"

lift_definition mrtabulate :: "mregex list \<Rightarrow> (mregex \<Rightarrow> 'b table) \<Rightarrow> (mregex, 'b table) mapping"
  is "\<lambda>ks f. (map_of (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) ks))" .

lemma lookup_tabulate:
  "distinct xs \<Longrightarrow> lookup (mrtabulate xs f) x = (if x \<in> set xs then f x else empty_table)"
  unfolding lookup_default_def lookup_def
  by transfer (auto simp: Let_def map_filter_def map_of_eq_None_iff o_def image_image dest!: map_of_SomeD
      split: if_splits option.splits)

definition update_matchP :: "nat \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> event_data table list \<Rightarrow> ts \<Rightarrow>
  event_data mr\<delta>aux \<Rightarrow> event_data table \<times> event_data mr\<delta>aux" where
  "update_matchP n I mr mrs rels nt aux =
    (let aux = (case [(t, mrtabulate mrs (\<lambda>mr.
        r\<delta> id rel rels mr \<union> (if t = nt then r\<epsilon>_strict n rels mr else {}))).
      (t, rel) \<leftarrow> aux, memR I (nt - t)]
      of [] \<Rightarrow> [(nt, mrtabulate mrs (r\<epsilon>_strict n rels))]
      | x # aux' \<Rightarrow> (if fst x = nt then x # aux'
                     else (nt, mrtabulate mrs (r\<epsilon>_strict n rels)) # x # aux'))
    in (foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux, memL I (nt - t)] {}, aux))"

definition update_matchF_base where
  "update_matchF_base n I mr mrs rels nt =
     (let X = mrtabulate mrs (l\<epsilon>_strict n rels)
     in ([(nt, rels, if memL I 0 then lookup X mr else empty_table)], X))"

definition update_matchF_step where
  "update_matchF_step I mr mrs nt = (\<lambda>(t, rels', rel) (aux', X).
     (let Y = mrtabulate mrs (l\<delta> id X rels')
     in ((t, rels', if mem I ((nt - t)) then rel \<union> lookup Y mr else rel) # aux', Y)))"

definition update_matchF :: "nat \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> event_data table list \<Rightarrow> ts \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> event_data ml\<delta>aux" where
  "update_matchF n I mr mrs rels nt aux =
     fst (foldr (update_matchF_step I mr mrs nt) aux (update_matchF_base n I mr mrs rels nt))"

fun eval_matchF :: "\<I> \<Rightarrow> mregex \<Rightarrow> ts \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> event_data table list \<times> event_data ml\<delta>aux" where
  "eval_matchF I mr nt [] = ([], [])"
| "eval_matchF I mr nt ((t, rels, rel) # aux) = (if \<not> memR I (nt - t) then
    (let (xs, aux) = eval_matchF I mr nt aux in (rel # xs, aux)) else ([], (t, rels, rel) # aux))"

primrec map_split where
  "map_split f [] = ([], [])"
| "map_split f (x # xs) =
    (let (y, z) = f x; (ys, zs) = map_split f xs
    in (y # ys, z # zs))"

fun eval_assignment :: "nat \<times> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> event_data tuple" where
  "eval_assignment (x, t) y = (y[x:=Some (meval_trm t y)])"

fun eval_constraint0 :: "mconstraint \<Rightarrow> event_data \<Rightarrow> event_data \<Rightarrow> bool" where
  "eval_constraint0 MEq x y = (x = y)"
| "eval_constraint0 MLess x y = (x < y)"
| "eval_constraint0 MLessEq x y = (x \<le> y)"

fun eval_constraint :: "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow> event_data tuple \<Rightarrow> bool" where
  "eval_constraint (t1, p, c, t2) x = (eval_constraint0 c (meval_trm t1 x) (meval_trm t2 x) = p)"

definition "lookahead_ts nts' nts ts t = hd (nts' @ rev (nts @ ts) @ [t])"

lemma lookahead_ts_code[code]: "lookahead_ts nts' nts ts t =
   (case nts' of t # _ \<Rightarrow> t
   | [] \<Rightarrow> (case ts of _ # _ \<Rightarrow> last ts
           | [] \<Rightarrow> (case nts of _ # _ \<Rightarrow> last nts
                   | [] \<Rightarrow> t)))"
  by (auto simp: lookahead_ts_def hd_append hd_rev split: list.splits)

primrec (in maux) meval :: "nat \<Rightarrow> ts list \<Rightarrow> Formula.database \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula \<Rightarrow>
    event_data table list \<times> ('msaux, 'muaux, 'mtaux) mformula" where
  "meval n ts db (MRel rel) = (replicate (length ts) (rel), MRel rel)"
| "meval n ts db (MPred e tms) = (map (\<lambda>X. (\<lambda>f. Table.tabulate f 0 n) ` Option.these
    (match tms ` X)) (case Mapping.lookup db e of None \<Rightarrow> replicate (length ts) empty_table | Some xs \<Rightarrow> xs), MPred e tms)"
| "meval n ts db (MLet p m \<phi> \<psi>) =
    (let (xs, \<phi>) = meval m ts db \<phi>; (ys, \<psi>) = meval n ts (Mapping.update p (map (image (map the)) xs) db) \<psi>
    in (ys, MLet p m \<phi> \<psi>))"
| "meval n ts db (MAnd V1 \<phi> pos V2 \<psi> buf) =
    (let (xs, \<phi>)   = meval n ts db \<phi>;
         (ys, \<psi>)   = meval n ts db \<psi>;
         (zs, buf) = mbuf2_take (\<lambda>(r1) (r2). (bin_join n V1 r1 pos V2 r2)) (mbuf2_add xs ys buf)
    in (zs, MAnd V1 \<phi> pos V2 \<psi> buf))"
| "meval n ts db (MAndAssign \<phi> conf) =
    (let (xs, \<phi>) = meval n ts db \<phi> in
    (map (\<lambda>(r). (eval_assignment conf ` r)) xs, MAndAssign \<phi> conf))"
| "meval n ts db (MAndRel \<phi> conf) =
    (let (xs, \<phi>) = meval n ts db \<phi> in (map (\<lambda>(r). (Set.filter (eval_constraint conf) r)) xs, MAndRel \<phi> conf))"
| "meval n ts db (MAndTrigger V_\<phi> \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux) = (let
    (as, \<phi>) = meval n ts db \<phi>;
    (xs, \<phi>') = meval n ts db \<phi>';
    (ys, \<psi>') = meval n ts db \<psi>';
    ((zs_trigger, aux), buf2, nts) = mbuf2t_take (\<lambda>r1 r2 t (zs, aux).
        let aux       = update_mtaux args t r1 r2 aux;
            (fv_z, z) = result_mtaux args aux
        in (zs @ [(fv_z, z)], aux)) ([], aux) (mbuf2_add xs ys buf2) (nts @ ts);
     \<comment> \<open>analogous to MAnd\<close>
    (zs, buf1) = mbuf2_take (\<lambda>r1 (V_trigger, r2).
        bin_join n V_\<phi> r1 True V_trigger r2 \<comment> \<open>fix pos=True for the and join\<close>
    ) (mbuf2_add as zs_trigger buf1)
    in
    (zs, MAndTrigger V_\<phi> \<phi> buf1 args \<phi>' \<psi>' buf2 nts aux)
)"
| "meval n ts db (MAnds A_pos A_neg L buf) =
    (let R = map (meval n ts db) L in
    let buf = mbufn_add (map fst R) buf in
    let (zs, buf) = mbufn_take (\<lambda>xs zs. zs @ [mmulti_join n A_pos A_neg xs]) [] buf in
    (zs, MAnds A_pos A_neg (map snd R) buf))"
| "meval n ts db (MOr \<phi> \<psi> buf) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>(r1) (r2). (r1 \<union> r2)) (mbuf2_add xs ys buf)
    in (zs, MOr \<phi> \<psi> buf))"
| "meval n ts db (MNeg \<phi>) =
    (let (xs, \<phi>) = meval n ts db \<phi> in (map (\<lambda>(r). (if r = empty_table then (unit_table n) else (empty_table))) xs, MNeg \<phi>))"
| "meval n ts db (MExists \<phi>) =
    (let (xs, \<phi>) = meval (Suc n) ts db \<phi> in (map (\<lambda>(r). (tl ` r)) xs, MExists \<phi>))"
| "meval n ts db (MAgg g0 y \<omega> b f \<phi>) =
    (let (xs, \<phi>) = meval (b + n) ts db \<phi> in (map (\<lambda>(r). (eval_agg n g0 y \<omega> b f r)) xs, MAgg g0 y \<omega> b f \<phi>))"
| "meval n ts db (MPrev I \<phi> first buf nts) =
    (let (xs, \<phi>) = meval n ts db \<phi>
    in if first \<and> ts = [] then ([], MPrev I \<phi> True (buf @ xs) (nts @ ts))
    else let (zs, buf, nts) = mprev_next I (buf @ xs) (nts @ ts)
      in (if first then (empty_table) # zs else zs, MPrev I \<phi> False buf nts))"
| "meval n ts db (MNext I \<phi> first nts) =
    (let (xs, \<phi>) = meval n ts db \<phi>;
      (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
      (zs, _, nts) = mprev_next I xs (nts @ ts)
    in (zs, MNext I \<phi> first nts))"
| "meval n ts db (MSince args \<phi> \<psi> buf nts aux) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      ((zs, aux), buf, nts) = mbuf2t_take (\<lambda>(r1) (r2) t (zs, aux).
        let (z, aux) = update_since args r1 r2 t aux
        in (zs @ [(z)], aux)) ([], aux) (mbuf2_add xs ys buf) (nts @ ts)
    in (zs, MSince args \<phi> \<psi> buf nts aux))"
| "meval n ts db (MUntil args \<phi> \<psi> buf nts t aux) = (let
      (xs, \<phi>) = meval n ts db \<phi>;
      (ys, \<psi>) = meval n ts db \<psi>;
      (aux, buf, nts') = mbuf2t_take (\<lambda>(r1) (r2) t aux.
        add_new_muaux args r1 r2 t aux
       ) aux (mbuf2_add xs ys buf) (nts @ ts);
      nt = lookahead_ts nts' nts ts t;
      (zs, aux) = eval_muaux args nt aux
    in (zs, MUntil args \<phi> \<psi> buf nts' nt aux))"
| "meval n ts db (MTrigger args \<phi> \<psi> buf nts aux) =
    (let (xs, \<phi>) = meval n ts db \<phi>; (ys, \<psi>) = meval n ts db \<psi>;
      ((zs, aux), buf, nts) = mbuf2t_take (\<lambda>(r1) (r2) t (zs, aux).
        let aux       = update_mtaux args t r1 r2 aux;
            (fv_z, z) = result_mtaux args aux
        in (zs @ [(z)], aux)) ([], aux) (mbuf2_add xs ys buf) (nts @ ts)
    in (zs, MTrigger args \<phi> \<psi> buf nts aux))"
| "meval n ts db (MMatchP I mr mrs \<phi>s buf nts aux) =
    (let (xss, \<phi>s) = map_split id (map (meval n ts db) \<phi>s);
      ((zs, aux), buf, nts) = mbufnt_take (\<lambda>rels t (zs, aux).
        let (z, aux) = update_matchP n I mr mrs rels t aux
        in (zs @ [z], aux)) ([], aux) (mbufn_add xss buf) (nts @ ts)
    in (zs, MMatchP I mr mrs \<phi>s buf nts aux))"
| "meval n ts db (MMatchF I mr mrs \<phi>s buf nts t aux) =
    (let (xss, \<phi>s) = map_split id (map (meval n ts db) \<phi>s);
      (aux, buf, nts') = mbufnt_take (\<lambda>rels t aux. update_matchF n I mr mrs rels t aux) aux (mbufn_add xss buf) (nts @ ts);
      nt = lookahead_ts nts' nts ts t;
      (zs, aux) = eval_matchF I mr nt aux
    in (zs, MMatchF I mr mrs \<phi>s buf nts' nt aux))"

definition (in maux) mstep :: "Formula.database \<times> ts \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate \<Rightarrow> (nat \<times> event_data table) list \<times> ('msaux, 'muaux, 'mtaux) mstate" where
  "mstep tdb st =
     (let (xs, m) = meval (mstate_n st) [snd tdb] (fst tdb) (mstate_m st)
     in (List.enumerate (mstate_i st) xs,
      \<lparr>mstate_i = mstate_i st + length xs, mstate_m = m, mstate_n = mstate_n st\<rparr>))"

subsection \<open>Verdict delay\<close>

context fixes \<sigma> :: Formula.trace begin

function (sequential) progress :: "(Formula.name \<rightharpoonup> nat) \<Rightarrow> Formula.formula \<Rightarrow> nat \<Rightarrow> nat" where
  "progress P (Formula.Pred e ts) j = (case P e of None \<Rightarrow> j | Some k \<Rightarrow> k)"
| "progress P (Formula.Let p \<phi> \<psi>) j = progress (P(p \<mapsto> progress P \<phi> j)) \<psi> j"
| "progress P (Formula.Eq t1 t2) j = j"
| "progress P (Formula.Less t1 t2) j = j"
| "progress P (Formula.LessEq t1 t2) j = j"
| "progress P (Formula.Neg \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Or \<phi> \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.And \<phi> \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.Ands l) j = (if l = [] then j else Min (set (map (\<lambda>\<phi>. progress P \<phi> j) l)))"
| "progress P (Formula.Exists \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Agg y \<omega> b f \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Prev I \<phi>) j = (if j = 0 then 0 else min (Suc (progress P \<phi> j)) j)"
| "progress P (Formula.Next I \<phi>) j = progress P \<phi> j - 1"
| "progress P (Formula.Since \<phi> I \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.Until \<phi> I \<psi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min (progress P \<phi> j) (progress P \<psi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
| "progress P (Formula.Trigger \<phi> I \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.Release \<phi> I \<psi>) j = (
    \<comment> \<open>for an actual implementation use Inf {i. \<forall>k. k < j \<and> k \<le> min (progress P \<phi> j) (progress P \<psi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)},
    for the rewrite rules the following is necessary as the rewrite rule of always leads to a
    funny term\<close>
    \<comment> \<open>the not bounded condition here just allows the rewrite formula to be applied in the else case\<close>
    if mem I 0 \<or> \<not>bounded I then
      Inf ({i. \<forall>k. k < j \<and> k \<le> min (progress P \<psi> j) (progress P \<phi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<union>
          {i. \<forall>k. k < j \<and> k \<le> progress P \<psi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)})
    else
      (progress P (release_safe_bounded \<phi> I \<psi>) j)
    )"
| "progress P (Formula.MatchP I r) j = min_regex_default (progress P) r j"
| "progress P (Formula.MatchF I r) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min_regex_default (progress P) r j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  by pat_completeness auto
termination
  using size'_and_release size'_Release size'_Or size'_release_aux
  by (relation "measure (\<lambda>(_, \<phi>, _). size' \<phi>)")
  (auto simp add: Nat.less_Suc_eq_le eventually_def Formula.TT_def Formula.FF_def dest!: sum_list_mem_leq[of _ _ size'] regex_atms_size')

(* sanity check for trigger progress *)

lemma progress_FF [simp]: "progress P Formula.FF j = j"
  unfolding Formula.FF_def
  by auto

lemma progress_TT [simp]: "progress P Formula.TT j = j"
  unfolding Formula.TT_def
  by auto

lemma progress_first [simp]: "progress P Formula.first j = j"
  unfolding Formula.first_def
  by auto

lemma progress_once [simp]: "progress P (once I \<phi>) j = min j (progress P \<phi> j)"
  unfolding once_def
  by auto

lemma progress_eventually[simp]: "progress P (eventually I \<phi>) j = Inf {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  unfolding eventually_def
  by (auto intro: arg_cong[where f = Inf])

lemma progress_eventually_once[simp]: "progress P (eventually I (once J \<phi>)) j = progress P (eventually I \<phi>) j"
  by (auto intro: arg_cong[where f = Inf])

lemma progress_historically_safe_0 [simp]: "progress P (historically_safe_0 I \<phi>) j = min j (
  if bounded I then
    (progress P \<phi> j) - 1 \<comment> \<open>? in in the past.\<close>
  else
    progress P \<phi> j
  )"
  unfolding historically_safe_0_def
  by auto

lemma progress_historically_safe_bounded [simp]: "progress P (historically_safe_bounded I \<phi>) j = min j (Inf {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)})"
proof -
  define A where "A =  {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  have "progress P \<phi> j \<in> A"
    unfolding A_def
    by auto
  then have "\<Sqinter> A \<le> progress P \<phi> j"
    by (simp add: cInf_lower)
  then  have " min (min j (local.progress P \<phi> j)) (\<Sqinter> A) =
    min j (\<Sqinter> A)"
    by auto
  moreover have "memR (int_remove_lower_bound I) = memR I"
    by (transfer) (auto)
  ultimately show ?thesis
    unfolding historically_safe_bounded_def A_def
    by auto
qed

lemma progress_historically_safe_unbounded [simp]: "progress P (historically_safe_unbounded I \<phi>) j = min j (progress P \<phi> j)"
  unfolding historically_safe_unbounded_def
  by auto

lemma memR_flip_int_double_upper: "memR I t \<Longrightarrow> memR (flip_int_double_upper I) t"
  by transfer auto

lemma Inf_leq:
  fixes X::"nat set"
  shows "X \<noteq> {} \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Inf Y \<le> Inf X"
  by (simp add: cInf_superset_mono)


lemma progress_always_safe_0 [simp]: "progress P (always_safe_0 I \<phi>) j =
  Inf {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
proof -
  have set_eq: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> Suc (local.progress P \<phi> j) \<and> k \<le> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)} =
        {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    by auto
  have subset: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<subseteq>
  {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    using memR_flip_int_double_upper
    by auto
  have "(local.progress P \<phi> j + 1) \<in> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    by auto
  then have non_empty: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<noteq> {}"
    by blast

  have "min (\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)})
     (\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}) =
    \<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    using Inf_leq[OF non_empty subset]
    by auto
  
  then show ?thesis
    using set_eq
    unfolding always_safe_0_def
    by auto
qed

lemma progress_nonempty: "{i. \<forall>k. k < j \<and> k \<le> n \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<noteq> {}"
  by (auto intro!: exI[of _ n])

lemma min_Inf:
  fixes X :: "nat set"
  assumes "X \<noteq> {}" "Y \<noteq> {}"
  shows "min (Inf X) (Inf Y) = Inf (X \<union> Y)"
proof -
  obtain x where x_def: "x = Inf X" "x \<in> X" "\<And>z. z \<in> X \<Longrightarrow> x \<le> z"
    using assms(1) cInf_lower
    by (auto simp add: Inf_nat_def1)
  obtain y where y_def: "y = Inf Y" "y \<in> Y" "\<And>z. z \<in> Y \<Longrightarrow> y \<le> z"
    using assms(2) cInf_lower
    by (auto simp add: Inf_nat_def1)
  have "min x y \<in> X \<union> Y" "\<And>z. z \<in> X \<union> Y \<Longrightarrow> min x y \<le> z"
    using x_def(2,3) y_def(2,3)
    by (fastforce simp: min_def)+
  then have "Inf (X \<union> Y) = min x y"
    unfolding Inf_nat_def
    by (rule Least_equality)
  then show ?thesis
    by (auto simp: x_def(1) y_def(1))
qed

lemma progress_eventually_or[simp]: "progress P (eventually I (Formula.Or \<phi> \<psi>)) j =
  min (progress P (eventually I \<phi>) j) (progress P (eventually I \<psi>) j)"
  unfolding progress_eventually min_Inf[OF progress_nonempty progress_nonempty]
  by (cases "progress P \<phi> j \<le> progress P \<psi> j") (auto intro: arg_cong[where ?f=Inf])

lemma diff_le_mono_cross: "m \<le> n \<Longrightarrow> l \<le> l' \<Longrightarrow> m - l' \<le> n - l" for m n l l' :: nat
  by auto

lemma subset_contrI: "(\<And>x. x \<notin> B \<Longrightarrow> x \<notin> A) \<Longrightarrow> A \<subseteq> B"
  by auto

lemma Inf_memR_conv: "\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> n \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} =
  (case j of 0 \<Rightarrow> 0 | Suc x \<Rightarrow> Inf {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)})"
  using memR_antimono[OF _ diff_le_mono[OF \<tau>_mono]]
  by (fastforce simp: cInf_eq_minimum less_Suc_eq_le split: nat.splits intro!: arg_cong[where ?f=Inf])

lemma min_x_Inf: "min x (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}) = \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
proof -
  {
    assume assm: "x < \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
    then have "x \<in> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
      by auto
    then have "x \<ge> \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
      by (simp add: cInf_lower)
    then have "False" using assm by auto
  }
  then show ?thesis
    by (meson min.absorb2 not_le_imp_less)
qed

lemma progress_eventually_double_upper[simp]: "(progress P (eventually I (eventually (int_remove_lower_bound I) \<phi>)) j) =
  (case j of 0 \<Rightarrow> 0
   | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)}) - \<tau> \<sigma> i)})"
proof -
  have "(progress P (eventually I (eventually (int_remove_lower_bound I) \<phi>)) j) =
    (case j of 0 \<Rightarrow> 0
     | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (min x (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)})) - \<tau> \<sigma> i)})"
  unfolding progress_eventually Inf_memR_conv
  by transfer' (auto split: nat.splits)
  moreover have "\<dots> = (case j of 0 \<Rightarrow> 0
     | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)}) - \<tau> \<sigma> i)})"
    by (auto simp: min_x_Inf split: nat.splits)
  finally show ?thesis .
qed

lemma progress_always_safe_bounded [simp]: "progress P (always_safe_bounded I \<phi>) j = (case j of 0 \<Rightarrow> 0
  | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)}) - \<tau> \<sigma> i)})"
proof -
  have "(local.progress P \<phi> j + 1) \<in> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    by auto
  then have non_empty: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<noteq> {}"
    by blast
  have subset: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<subseteq> {i. \<forall>k. k < j \<and> k \<le> j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> \<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (int_remove_lower_bound I) (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<longrightarrow>
                 memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    by auto
  have min_eq: "min (\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)})
     (\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> \<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (int_remove_lower_bound I) (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<longrightarrow>
                 memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}) =
    \<Sqinter> {i. \<forall>k. k < j \<and> k \<le> j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> \<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (int_remove_lower_bound I) (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<longrightarrow>
                 memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}
  "
    using Inf_leq[OF non_empty subset]
    by auto

  have sub: "\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<le>
    \<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    using memR_flip_int_double_upper
    by (auto intro: Inf_leq[OF progress_nonempty])

  have "progress P (always_safe_bounded I \<phi>) j = progress P (eventually I (formula.Or (once (int_remove_lower_bound I) \<phi>) (eventually (int_remove_lower_bound I) \<phi>))) j"
    unfolding always_safe_bounded_def
    by (auto simp add: min_eq)
  moreover have "\<dots> = min (local.progress P (Formula.eventually I \<phi>) j) (case j of 0 \<Rightarrow> 0
   | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)}) - \<tau> \<sigma> i)})"
    unfolding progress_eventually_or progress_eventually_once progress_eventually_double_upper
    by auto
  moreover have "\<dots> = (case j of 0 \<Rightarrow> 0
   | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)}) - \<tau> \<sigma> i)})"
    unfolding progress_eventually Inf_memR_conv
    apply (auto split: nat.splits)
    by (metis min_x_Inf min.idem)
  ultimately show ?thesis
    unfolding progress_eventually
    by auto
qed

lemma progress_release_rewrite_0:
  assumes "mem I 0"
  shows "progress P (release_safe_0 \<phi> I \<psi>) j = progress P (formula.Release \<phi> I \<psi>) j"
proof -
  define A where "A = {i. \<forall>k. k < j \<and> k \<le> min (progress P \<psi> j) (progress P \<phi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  define B where "B = {i. \<forall>k. k < j \<and> k \<le> progress P \<psi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"

  have "progress P (release_safe_0 \<phi> I \<psi>) j = min (progress P (formula.Until \<psi> I (formula.And \<psi> \<phi>)) j) (progress P (always_safe_0 I \<psi>) j)"
    unfolding release_safe_0_def
    by auto
  moreover have "progress P (formula.Until \<psi> I (formula.And \<psi> \<phi>)) j = Inf A"
    unfolding A_def
    by auto
  moreover have "progress P (always_safe_0 I \<psi>) j = Inf B"
    unfolding B_def
    by auto
  ultimately have progress_eq: "progress P (release_safe_0 \<phi> I \<psi>) j = min (Inf A) (Inf B)"
    by auto

  have
    "(min (local.progress P \<psi> j) (local.progress P \<phi> j)) \<in> A"
    "progress P \<psi> j \<in> B"
    unfolding A_def B_def
    by auto
  then have non_empty: 
    "A \<noteq> {}"
    "B \<noteq> {}"
    by auto

  then show ?thesis
    using progress_eq min_Inf[OF non_empty] assms
    unfolding A_def B_def
    by auto
qed

lemma progress_release_safe_bounded_evtl: "min (progress P (Formula.eventually I Formula.TT) j) (progress P (release_safe_bounded \<phi> I \<psi>) j) = progress P (release_safe_bounded \<phi> I \<psi>) j"
  unfolding release_safe_bounded_def
  by auto

lemma progress_eventually_subformulas:
  assumes "progress P \<phi> j \<le> progress P \<psi> j"
  shows "(progress P (Formula.eventually I \<phi>) j) \<le> (progress P (Formula.eventually I \<psi>) j)"
proof -
  define A where "A = {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  define B where "B = {i. \<forall>k. k < j \<and> k \<le> progress P \<psi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  have
    "progress P \<psi> j \<in> B"
    unfolding B_def
    by auto
  then have B_props: "B \<noteq> {}"
    by auto

  {
    fix i
    assume "i \<in> B"
    then have "\<forall>k. k < j \<and> k \<le> progress P \<psi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      unfolding B_def
      by auto
    then have "\<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      using assms
      by auto
    then have "i \<in> A"
      unfolding A_def
      by auto
  }
  then have "B \<subseteq> A" by blast
  then have "\<Sqinter> A \<le> \<Sqinter> B"
    using Inf_leq[OF B_props]
    by auto
  moreover have
    "progress P (Formula.eventually I \<phi>) j = \<Sqinter> A"
    "progress P (Formula.eventually I \<psi>) j = \<Sqinter> B"
    unfolding A_def B_def
    by auto
  ultimately show ?thesis by auto
qed

lemma progress_trigger_0_lower_bound: "progress P (trigger_safe_0 \<phi> I \<psi>) j \<le> progress P (formula.Trigger \<phi> I \<psi>) j"
  by (auto simp add: trigger_safe_0_def)

lemma progress_trigger_unbounded_lower_bound: "progress P (trigger_safe_unbounded \<phi> I \<psi>) j \<le> progress P (formula.Trigger \<phi> I \<psi>) j"
  by (auto simp add: trigger_safe_unbounded_def)

lemma progress_and_trigger_unbounded_lower_bound: "progress P (and_trigger_safe_unbounded \<alpha> \<phi> I \<psi>) j \<le> progress P (formula.And \<alpha> (formula.Trigger \<phi> I \<psi>)) j"
proof -
  have
    "progress P (trigger_safe_unbounded \<phi> I \<psi>) j \<le> progress P \<phi> j"
    "progress P (trigger_safe_unbounded \<phi> I \<psi>) j \<le> progress P \<psi> j"
    using progress_trigger_unbounded_lower_bound
    by auto
  then show ?thesis
    by (auto simp add: and_trigger_safe_unbounded_def)
qed

lemma progress_trigger_bounded_lower_bound: "progress P (trigger_safe_bounded \<phi> I \<psi>) j \<le> progress P (formula.Trigger \<phi> I \<psi>) j"
proof -
  define A where "A = {i. \<forall>k. k < j \<and> k \<le> progress P \<psi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"

  have leq_\<phi>: "0 < j \<Longrightarrow> min (min (min j (\<Sqinter> A))
            (min j (local.progress P \<phi> j)))
       (min (Suc (min (local.progress P \<phi> j) (local.progress P \<psi> j))) j)
      \<le> local.progress P \<phi> j"
    by auto
  have leq_\<psi>: "0 < j \<Longrightarrow> min (min (min j (\<Sqinter> A))
            (min j (local.progress P \<phi> j)))
       (min (Suc (min (local.progress P \<phi> j) (local.progress P \<psi> j))) j)
      \<le> local.progress P \<psi> j"
  proof -
    have "progress P \<psi> j \<in> A"
      unfolding A_def
      by auto
    then have "Inf A \<le> progress P \<psi> j"
      by (simp add: cInf_lower)
    then show ?thesis by auto
  qed

  show ?thesis 
    apply (auto simp add: trigger_safe_bounded_def)
    using leq_\<phi> leq_\<psi>
    unfolding A_def
    by blast+
qed

lemma progress_and_trigger_bounded_lower_bound: "progress P (and_trigger_safe_bounded \<alpha> \<phi> I \<psi>) j \<le> progress P (formula.And \<alpha> (formula.Trigger \<phi> I \<psi>)) j"
proof -
  have
    "progress P (trigger_safe_bounded \<phi> I \<psi>) j \<le> progress P \<phi> j"
    "progress P (trigger_safe_bounded \<phi> I \<psi>) j \<le> progress P \<psi> j"
    using progress_trigger_bounded_lower_bound
    by auto
  then show ?thesis
    by (auto simp add: and_trigger_safe_bounded_def)
qed

lemma progress_and_release_rewrite_bounded:
  assumes "\<not> mem I 0" "bounded I"
  shows "Monitor.progress \<sigma> P (and_release_safe_bounded \<phi> \<phi>' I \<psi>') j = progress P (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) j"
proof -
  have "progress P (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) j = min (progress P \<phi> j) (min (progress P (Formula.eventually I Formula.TT) j) (progress P (release_safe_bounded \<phi>' I \<psi>') j))"
    using assms
    by (auto simp only: progress_release_safe_bounded_evtl[of P I j \<phi>' \<psi>'] progress.simps split: if_splits)
  then show ?thesis
    using assms
    unfolding and_release_safe_bounded_def
    by auto
qed

(*lemma progress_historically_safe_bounded [simp]: "progress P (historically_safe_bounded I \<phi>) j = j"
  unfolding historically_safe_bounded_def
  by auto*)

(*lemma "progress P (Formula.Trigger \<phi> I \<psi>) j = progress P (trigger_safe_0 \<phi> I \<psi>) j"
  unfolding trigger_safe_0_def
  by (auto split: if_splits)*)

definition "progress_regex P = min_regex_default (progress P)"

declare progress.simps[simp del]
lemmas progress_simps[simp] = progress.simps[folded progress_regex_def[THEN fun_cong, THEN fun_cong]]

end

definition "pred_mapping Q = pred_fun (\<lambda>_. True) (pred_option Q)"
definition "rel_mapping Q = rel_fun (=) (rel_option Q)"

lemma pred_mapping_alt: "pred_mapping Q P = (\<forall>p \<in> dom P. Q (the (P p)))"
  unfolding pred_mapping_def pred_fun_def option.pred_set dom_def
  by (force split: option.splits)

lemma rel_mapping_alt: "rel_mapping Q P P' = (dom P = dom P' \<and> (\<forall>p \<in> dom P. Q (the (P p)) (the (P' p))))"
  unfolding rel_mapping_def rel_fun_def rel_option_iff dom_def
  by (force split: option.splits)

lemma rel_mapping_map_upd[simp]: "Q x y \<Longrightarrow> rel_mapping Q P P' \<Longrightarrow> rel_mapping Q (P(p \<mapsto> x)) (P'(p \<mapsto> y))"
  by (auto simp: rel_mapping_alt)

lemma pred_mapping_map_upd[simp]: "Q x \<Longrightarrow> pred_mapping Q P \<Longrightarrow> pred_mapping Q (P(p \<mapsto> x))"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_empty[simp]: "pred_mapping Q Map.empty"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_mono: "pred_mapping Q P \<Longrightarrow> Q \<le> R \<Longrightarrow> pred_mapping R P"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_mono_strong: "pred_mapping Q P \<Longrightarrow>
  (\<And>p. p \<in> dom P \<Longrightarrow> Q (the (P p)) \<Longrightarrow> R (the (P p))) \<Longrightarrow> pred_mapping R P"
  by (auto simp: pred_mapping_alt)

lemma progress_mono_gen: "j \<le> j' \<Longrightarrow> rel_mapping (\<le>) P P' \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j'"
proof (induction P \<phi> j arbitrary: P P' rule: progress.induct[of _ \<sigma>])
case (1 P e ts j)
  then show ?case
    by (force simp: rel_mapping_alt dom_def split: option.splits)
next
  case (15 P \<phi> I \<psi> j)
   from 15(1,2)[of P P'] 15(3-) show ?case
    by (auto 0 3 dest: memR_nonzeroD less_\<tau>D spec[of _ j'] intro!: cInf_superset_mono)
next
  case (17 P \<phi> I \<psi> j)
  then show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
     from 17(1,2)[of P P'] 17(4-) show ?thesis
       by (auto 0 3 dest: memR_nonzeroD less_\<tau>D spec[of _ j'] intro!: cInf_superset_mono)
  next
    case False
    then show ?thesis using 17 by auto
  qed
next
  case (19 P I r j)
  from 19(1)[of _ P P'] 19(2-) show ?case
    apply (auto 0 3 simp: Min_le_iff progress_regex_def dest: memR_nonzeroD less_\<tau>D spec[of _ j']
      elim!: order_trans less_le_trans intro!: cInf_superset_mono)
    by (metis ex_in_conv le_trans less_le_trans)
qed (force simp: Min_le_iff progress_regex_def split: option.splits)+

lemma rel_mapping_reflp: "reflp Q \<Longrightarrow> rel_mapping Q P P"
  by (auto simp: rel_mapping_alt reflp_def)

lemmas progress_mono = progress_mono_gen[OF _ rel_mapping_reflp[unfolded reflp_def], simplified]

lemma progress_le_gen: "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> P \<phi> j \<le> j"
proof (induction P \<phi> j rule: progress.induct[of _ \<sigma>])
  case (1 P e ts j)
  then show ?case
     by (auto simp: pred_mapping_alt dom_def split: option.splits)
next
  case (9 P l j)
  then show ?case
     by (auto simp: image_iff intro!: Min.coboundedI[where a="progress \<sigma> P (hd l) j", THEN order_trans])
next
  case (15 P \<phi> I \<psi> j)
  then show ?case
    by (auto intro!: cInf_lower)
next
  case (17 P \<phi> I \<psi> j)
  then show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    then show ?thesis
      using 17 by (auto intro!: cInf_lower)
  next
    case False
    then show ?thesis using 17 by auto
  qed
next
  case (19 P I r j)
  then show ?case
    by (auto intro!: cInf_lower)
qed (force simp: Min_le_iff progress_regex_def split: option.splits)+

lemma progress_le: "progress \<sigma> Map.empty \<phi> j \<le> j"
  using progress_le_gen[of _ Map.empty] by auto

lemma progress_0_gen[simp]:
  "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> progress \<sigma> P \<phi> 0 = 0"
  using progress_le_gen[of 0 P] by auto

lemma progress_0[simp]:
  "progress \<sigma> Map.empty \<phi> 0 = 0"
  by (auto simp: pred_mapping_alt)

definition max_mapping :: "('b \<Rightarrow> 'a option) \<Rightarrow> ('b \<Rightarrow> 'a option) \<Rightarrow> 'b \<Rightarrow> ('a :: linorder) option" where
  "max_mapping P P' x = (case (P x, P' x) of
    (None, None) \<Rightarrow> None
  | (Some x, None) \<Rightarrow> None
  | (None, Some x) \<Rightarrow> None
  | (Some x, Some y) \<Rightarrow> Some (max x y))"

definition Max_mapping :: "('b \<Rightarrow> 'a option) set \<Rightarrow> 'b \<Rightarrow> ('a :: linorder) option" where
  "Max_mapping Ps x = (if (\<forall>P \<in> Ps. P x \<noteq> None) then Some (Max ((\<lambda>P. the (P x)) ` Ps)) else None)"

lemma dom_max_mapping[simp]: "dom (max_mapping P1 P2) = dom P1 \<inter> dom P2"
  unfolding max_mapping_def by (auto split: option.splits)

lemma dom_Max_mapping[simp]: "dom (Max_mapping X) = (\<Inter>P \<in> X. dom P)"
  unfolding Max_mapping_def by (auto split: if_splits)

lemma Max_mapping_coboundedI:
  assumes "finite X" "\<forall>Q \<in> X. dom Q = dom P" "P \<in> X"
  shows "rel_mapping (\<le>) P (Max_mapping X)"
  unfolding rel_mapping_alt
proof (intro conjI ballI)
  from assms(3) have "X \<noteq> {}" by auto
  then show "dom P = dom (Max_mapping X)" using assms(2) by auto
next
  fix p
  assume "p \<in> dom P"
  with assms show "the (P p) \<le> the (Max_mapping X p)"
    by (force simp add: Max_mapping_def intro!: Max.coboundedI imageI)
qed

lemma rel_mapping_trans: "P OO Q \<le> R \<Longrightarrow>
  rel_mapping P P1 P2 \<Longrightarrow> rel_mapping Q P2 P3 \<Longrightarrow> rel_mapping R P1 P3"
  by (force simp: rel_mapping_alt dom_def set_eq_iff)

abbreviation range_mapping :: "nat \<Rightarrow> nat \<Rightarrow> ('b \<Rightarrow> nat option) \<Rightarrow> bool" where
  "range_mapping i j P \<equiv> pred_mapping (\<lambda>x. i \<le> x \<and> x \<le> j) P"

lemma range_mapping_relax:
  "range_mapping i j P \<Longrightarrow> i' \<le> i \<Longrightarrow> j' \<ge> j \<Longrightarrow> range_mapping i' j' P"
  by (auto simp: pred_mapping_alt dom_def set_eq_iff max_mapping_def split: option.splits)

lemma range_mapping_max_mapping[simp]:
  "range_mapping i j1 P1 \<Longrightarrow> range_mapping i j2 P2 \<Longrightarrow> range_mapping i (max j1 j2) (max_mapping P1 P2)"
  by (auto simp: pred_mapping_alt dom_def set_eq_iff max_mapping_def split: option.splits)

lemma range_mapping_Max_mapping[simp]:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<forall>x\<in>X. range_mapping i (j x) (P x) \<Longrightarrow> range_mapping i (Max (j ` X)) (Max_mapping (P ` X))"
  by (force simp: pred_mapping_alt Max_mapping_def dom_def image_iff
      intro!: Max_ge_iff[THEN iffD2] split: if_splits)

lemma pred_mapping_le:
  "pred_mapping ((\<le>) i) P1 \<Longrightarrow> rel_mapping (\<le>) P1 P2 \<Longrightarrow> pred_mapping ((\<le>) (i :: nat)) P2"
  by (force simp: rel_mapping_alt pred_mapping_alt dom_def set_eq_iff)

lemma pred_mapping_le':
  "pred_mapping ((\<le>) j) P1 \<Longrightarrow> i \<le> j \<Longrightarrow> rel_mapping (\<le>) P1 P2 \<Longrightarrow> pred_mapping ((\<le>) (i :: nat)) P2"
  by (force simp: rel_mapping_alt pred_mapping_alt dom_def set_eq_iff)

lemma max_mapping_cobounded1: "dom P1 \<subseteq> dom P2 \<Longrightarrow> rel_mapping (\<le>) P1 (max_mapping P1 P2)"
  unfolding max_mapping_def rel_mapping_alt by (auto simp: dom_def split: option.splits)

lemma max_mapping_cobounded2: "dom P2 \<subseteq> dom P1 \<Longrightarrow> rel_mapping (\<le>) P2 (max_mapping P1 P2)"
  unfolding max_mapping_def rel_mapping_alt by (auto simp: dom_def split: option.splits)

lemma max_mapping_fun_upd2[simp]:
  "max_mapping P1 (P2(p := y))(p \<mapsto> x) = (max_mapping P1 P2)(p \<mapsto> x)"
  by (auto simp: max_mapping_def)

lemma rel_mapping_max_mapping_fun_upd: "dom P2 \<subseteq> dom P1 \<Longrightarrow> p \<in> dom P2 \<Longrightarrow> the (P2 p) \<le> y \<Longrightarrow>
  rel_mapping (\<le>) P2 (max_mapping P1 P2(p \<mapsto> y))"
  by (auto simp: rel_mapping_alt max_mapping_def split: option.splits)

(* as soon as release is implemented natively, this function can be removed.
   it is only used for it's induction rule
*)

function (sequential) dummy :: "Formula.formula \<Rightarrow> bool" where
  "dummy (Formula.Pred e ts) = True"
| "dummy (Formula.Let p \<phi> \<psi>) = (dummy \<phi> \<and> dummy \<psi>)"
| "dummy (Formula.Eq t1 t2) = True"
| "dummy (Formula.Less t1 t2) = True"
| "dummy (Formula.LessEq t1 t2) = True"
| "dummy (Formula.Neg \<phi>) = dummy \<phi>"
| "dummy (Formula.Or \<phi> \<psi>) = (dummy \<phi> \<and> dummy \<psi>)"
| "dummy (Formula.And \<phi> \<psi>) = (dummy \<phi> \<and> dummy \<psi>)"
| "dummy (Formula.Ands l) = fold (\<and>) (map (\<lambda>\<phi>. dummy \<phi>) l) True"
| "dummy (Formula.Exists \<phi>) = dummy \<phi>"
| "dummy (Formula.Agg y \<omega> b f \<phi>) = dummy \<phi>"
| "dummy (Formula.Prev I \<phi>) = dummy \<phi>"
| "dummy (Formula.Next I \<phi>) = dummy \<phi>"
| "dummy (Formula.Since \<phi> I \<psi>) = (dummy \<phi> \<and> dummy \<psi>)"
| "dummy (Formula.Until \<phi> I \<psi>) = (dummy \<phi> \<and> dummy \<psi>)"
| "dummy (Formula.Trigger \<phi> I \<psi>) = (dummy \<phi> \<and> dummy \<psi>)"
| "dummy (Formula.Release \<phi> I \<psi>) = (
    if mem I 0 \<or> \<not>bounded I then
      (dummy \<phi>) \<and> (dummy \<psi>)
    else
      (dummy (release_safe_bounded \<phi> I \<psi>))
    )"
| "dummy (Formula.MatchP I r) = Regex.pred_regex dummy r"
| "dummy (Formula.MatchF I r) =Regex.pred_regex dummy r"
  by pat_completeness auto
termination
  using size'_and_release size'_Release size'_Or size'_release_aux
  by (relation "measure size'")
  (auto simp add: Nat.less_Suc_eq_le eventually_def Formula.TT_def Formula.FF_def dest!: sum_list_mem_leq[of _ _ size'] regex_atms_size')

lemma progress_ge_gen: "Formula.future_bounded \<phi> \<Longrightarrow>
   \<exists>P j. dom P = S \<and> range_mapping i j P \<and> i \<le> progress \<sigma> P \<phi> j"
proof (induction \<phi> arbitrary: i S rule: dummy.induct)
  case (1 e ts)
then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"])
      (auto split: option.splits if_splits simp: rel_mapping_alt pred_mapping_alt dom_def)
next
  case (2 p \<phi> \<psi>)
  from 2 obtain P2 j2 where P2: "dom P2 = insert p S" "range_mapping i j2 P2"
    "i \<le> progress \<sigma> P2 \<psi> j2"
    by (atomize_elim, intro 2(2)) (force simp: pred_mapping_alt rel_mapping_alt dom_def)+
  from 2 obtain P1 j1 where P1: "dom P1 = S" "range_mapping (the (P2 p)) j1 P1"
    "the (P2 p) \<le> progress \<sigma> P1 \<phi> j1"
    by (atomize_elim, intro 2(1)) auto
  let ?P12 = "max_mapping P1 P2"
  from P1 P2 have le1: "progress \<sigma> P1 \<phi> j1 \<le> progress \<sigma> (?P12(p := P1 p)) \<phi> (max j1 j2)"
    by (intro progress_mono_gen) (auto simp: rel_mapping_alt max_mapping_def)
  from P1 P2 have le2: "progress \<sigma> P2 \<psi> j2 \<le> progress \<sigma> (?P12(p \<mapsto> progress \<sigma> P1 \<phi> j1)) \<psi> (max j1 j2)"
    by (intro progress_mono_gen) (auto simp: rel_mapping_alt max_mapping_def)
  show ?case
    unfolding progress.simps
  proof (intro exI[of _ "?P12(p := P1 p)"] exI[of _ "max j1 j2"] conjI)
    show "dom (?P12(p := P1 p)) = S"
      using P1 P2 by (auto simp: dom_def max_mapping_def)
  next
    show "range_mapping i (max j1 j2) (?P12(p := P1 p))"
      using P1 P2 by (force simp add: pred_mapping_alt dom_def max_mapping_def split: option.splits)
  next
    have "i \<le> progress \<sigma> P2 \<psi> j2" by fact
    also have "... \<le> progress \<sigma> (?P12(p \<mapsto> progress \<sigma> P1 \<phi> j1)) \<psi> (max j1 j2)"
      using le2 by blast
    also have "... \<le> progress \<sigma> (?P12(p := P1 p)(p\<mapsto>progress \<sigma> (?P12(p := P1 p)) \<phi> (max j1 j2))) \<psi> (max j1 j2)"
      by (auto intro!: progress_mono_gen simp: le1 rel_mapping_alt)
    finally show "i \<le> ..." .
  qed
next
  case (3 t1 t2)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) (auto split: if_splits simp: pred_mapping_alt)
next
  case (4 t1 t2)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) (auto split: if_splits simp: pred_mapping_alt)
next
  case (5 t1 t2)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) (auto split: if_splits simp: pred_mapping_alt)
next
  case (7 \<phi>1 \<phi>2)
  from 7(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using 7(1)[of S i] by auto
  moreover
  from 7(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using 7(2)[of S i] by auto
  ultimately have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Or \<phi>1 \<phi>2) (max j1 j2)"
    by (auto 0 3 elim!: order.trans[OF _ progress_mono_gen] intro: max_mapping_cobounded1 max_mapping_cobounded2)
  with P1 P2 show ?case by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) auto
next
  case (8 \<phi>1 \<phi>2)
  from 8(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using 8(1)[of S i] by auto
  moreover
  from 8(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using 8(2)[of S i] by auto
  ultimately have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.And \<phi>1 \<phi>2) (max j1 j2)"
    by (auto 0 3 elim!: order.trans[OF _ progress_mono_gen] intro: max_mapping_cobounded1 max_mapping_cobounded2)
  with P1 P2 show ?case by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) auto
next
  case (9 l)
  show ?case proof (cases "l = []")
    case True
    then show ?thesis
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"])
        (auto split: if_splits simp: pred_mapping_alt)
  next
    case False
    then obtain \<phi> where "\<phi> \<in> set l" by (cases l) auto
    from 9(2) have "\<forall>\<phi>\<in>set l. Formula.future_bounded \<phi>"
      by (simp add: list.pred_set)
    { fix \<phi>
      assume "\<phi> \<in> set l"
      with 9(2) obtain P j where "dom P = S" "range_mapping i j P" "i \<le> progress \<sigma> P \<phi> j"
        by (atomize_elim, intro 9(1)[of \<phi> S i]) (auto simp: list.pred_set)
      then have "\<exists>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) \<and> i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)"
        (is "\<exists>Pj. ?P Pj")
        by (intro exI[of _ "(P, j)"]) auto
    }
    then have "\<forall>\<phi>\<in>set l. \<exists>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) \<and> i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)"
      (is "\<forall>\<phi>\<in>set l. \<exists>Pj. ?P Pj \<phi>")
      by blast
    with 9(1) 9(2) False have "\<exists>Pjf. \<forall>\<phi>\<in>set l. ?P (Pjf \<phi>) \<phi>"
      by (auto simp: Ball_def intro: choice)
    then obtain Pjf where Pjf: "\<forall>\<phi>\<in>set l. ?P (Pjf \<phi>) \<phi>" ..
    define Pf where "Pf = fst o Pjf"
    define jf where "jf = snd o Pjf"
    have *: "dom (Pf \<phi>) = S" "range_mapping i (jf \<phi>) (Pf \<phi>)" "i \<le> progress \<sigma> (Pf \<phi>) \<phi> (jf \<phi>)"
      if "\<phi> \<in> set l" for \<phi>
      using Pjf[THEN bspec, OF that] unfolding Pf_def jf_def by auto
    with False show ?thesis
      unfolding progress.simps eq_False[THEN iffD2, OF False] if_False
      by ((subst Min_ge_iff; simp add: False),
          intro exI[where x="MAX \<phi>\<in>set l. jf \<phi>"] exI[where x="Max_mapping (Pf ` set l)"]
          conjI ballI order.trans[OF *(3) progress_mono_gen] Max_mapping_coboundedI)
        (auto simp: False *[OF \<open>\<phi> \<in> set l\<close>] \<open>\<phi> \<in> set l\<close>)
  qed
next
  case (12 I \<phi>)
  then obtain P j where "dom P = S" "range_mapping i j P" "i \<le> progress \<sigma> P \<phi> j"
    by (atomize_elim, intro 12(1)) (auto simp: pred_mapping_alt dom_def)
  with 12(2) have
    "dom P = S \<and> range_mapping i (max i j) P \<and> i \<le> progress \<sigma> P (formula.Prev I \<phi>) (max i j)"
    by (auto simp: le_Suc_eq max_def pred_mapping_alt split: if_splits
        elim: order.trans[OF _ progress_mono])
  then show ?case by blast
next
  case (13 I \<phi>)
  then obtain P j where "dom P = S" "range_mapping (Suc i) j P" "Suc i \<le> progress \<sigma> P \<phi> j"
    by (atomize_elim, intro 13(1)) (auto simp: pred_mapping_alt dom_def)
  then show ?case
    by (intro exI[of _ P] exI[of _ j]) (auto 0 3 simp: pred_mapping_alt dom_def)
next
  case (14 \<phi>1 I \<phi>2)
  from 14(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using 14(1)[of S i] by auto
  moreover
  from 14(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using 14(2)[of S i] by auto
  ultimately have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Since \<phi>1 I \<phi>2) (max j1 j2)"
    by (auto elim!: order.trans[OF _ progress_mono_gen] simp: max_mapping_cobounded1 max_mapping_cobounded2)
  with P1 P2 show ?case by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"])
      (auto elim!: pred_mapping_le intro: max_mapping_cobounded1)
next
  case (15 \<phi>1 I \<phi>2)
  from 15(3) obtain m where "\<not> memR I m"
    by (auto simp: bounded_memR)
  then obtain i' where "i < i'" and 1: "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  from 15(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping (Suc i') j1 P1" "Suc i' \<le> progress \<sigma> P1 \<phi>1 j1"
    by (atomize_elim, intro 15(1)) (auto simp: pred_mapping_alt dom_def)
  from 15(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping (Suc i') j2 P2" "Suc i' \<le> progress \<sigma> P2 \<phi>2 j2"
    by (atomize_elim, intro 15(2)) (auto simp: pred_mapping_alt dom_def)
  let ?P12 = "max_mapping P1 P2"
  have "i \<le> progress \<sigma> ?P12 (Formula.Until \<phi>1 I \<phi>2) (max j1 j2)"
    unfolding progress.simps
  proof (intro cInf_greatest, goal_cases nonempty greatest)
    case nonempty
    then show ?case
      by (auto simp: trans_le_add1[OF \<tau>_mono] intro!: exI[of _ "max j1 j2"])
  next
    case (greatest x)
    from P1(2,3) have "i' < j1"
      by (auto simp: less_eq_Suc_le intro!: progress_le_gen elim!: order.trans pred_mapping_mono_strong)
    then have "i' < max j1 j2" by simp
    have "progress \<sigma> P1 \<phi>1 j1 \<le> progress \<sigma> ?P12 \<phi>1 (max j1 j2)"
      using P1(1) P2(1) by (auto intro!: progress_mono_gen max_mapping_cobounded1)
    moreover have "progress \<sigma> P2 \<phi>2 j2 \<le> progress \<sigma> ?P12 \<phi>2 (max j1 j2)"
      using P1(1) P2(1) by (auto intro!: progress_mono_gen max_mapping_cobounded2)
    ultimately have "i' \<le> min (progress \<sigma> ?P12 \<phi>1 (max j1 j2)) (progress \<sigma> ?P12 \<phi>2 (max j1 j2))"
      using P1(3) P2(3) by simp
    with greatest \<open>i' < max j1 j2\<close> have "memR I (\<tau> \<sigma> i' - \<tau> \<sigma> x)"
      by simp
    with 1 have "\<tau> \<sigma> i < \<tau> \<sigma> x"
      by (auto 0 3 elim: contrapos_np)
    then show ?case by (auto dest!: less_\<tau>D)
  qed
  with P1 P2 \<open>i < i'\<close> show ?case
    by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) (auto simp: range_mapping_relax)
next
  case (16 \<phi>1 I \<phi>2)
  have size':
    "size' \<phi>1 \<le> size' \<phi>1 + size' \<phi>2"
    "size' \<phi>2 \<le> size' \<phi>1 + size' \<phi>2"
    by auto
  from 16(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using 16(1)[of S i] by auto
  moreover
  from 16(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using 16(2)[of S i] by auto
  ultimately have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Since \<phi>1 I \<phi>2) (max j1 j2)"
    by (auto elim!: order.trans[OF _ progress_mono_gen] simp: max_mapping_cobounded1 max_mapping_cobounded2)
  with P1 P2 show ?case by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"])
      (auto elim!: pred_mapping_le intro: max_mapping_cobounded1)
next
  case (17 \<phi>1 I \<phi>2)
  from 17(4) have "bounded (flip_int_double_upper I)"
    by (transfer') auto
  then obtain m where "\<not> memR (flip_int_double_upper I) m"
    by (auto simp: bounded_memR)

  then obtain i' where "i < i'" and 1: "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  then have not_mem_I: "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using memR_flip_int_double_upper
    by auto

  show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    from 17(4) True obtain P1 j1 where P1: "dom P1 = S" "range_mapping (Suc i') j1 P1" "Suc i' \<le> progress \<sigma> P1 \<phi>1 j1"
      by (atomize_elim, intro 17(1)) (auto simp: pred_mapping_alt dom_def)
    from 17(4) True obtain P2 j2 where P2: "dom P2 = S" "range_mapping (Suc i') j2 P2" "Suc i' \<le> progress \<sigma> P2 \<phi>2 j2"
      by (atomize_elim, intro 17(2)) (auto simp: pred_mapping_alt dom_def)
    let ?P12 = "max_mapping P1 P2"

    have "i \<le> progress \<sigma> ?P12 (Formula.Release \<phi>1 I \<phi>2) (max j1 j2)"
      unfolding progress.simps if_P[OF True]
    proof (intro cInf_greatest, goal_cases nonempty greatest)
      case nonempty
      then show ?case
        by (auto simp: trans_le_add1[OF \<tau>_mono] intro!: exI[of _ "max j1 j2"])
    next
      case (greatest x)
      from P1(2,3) have "i' < j1"
        by (auto simp: less_eq_Suc_le intro!: progress_le_gen elim!: order.trans pred_mapping_mono_strong)
      then have "i' < max j1 j2" by simp
      have "progress \<sigma> P1 \<phi>1 j1 \<le> progress \<sigma> ?P12 \<phi>1 (max j1 j2)"
        using P1(1) P2(1) by (auto intro!: progress_mono_gen max_mapping_cobounded1)
      moreover have "progress \<sigma> P2 \<phi>2 j2 \<le> progress \<sigma> ?P12 \<phi>2 (max j1 j2)"
        using P1(1) P2(1) by (auto intro!: progress_mono_gen max_mapping_cobounded2)
      ultimately have "i' \<le> min (progress \<sigma> ?P12 \<phi>1 (max j1 j2)) (progress \<sigma> ?P12 \<phi>2 (max j1 j2))"
        using P1(3) P2(3) by simp
      with greatest \<open>i' < max j1 j2\<close> have
        "memR (flip_int_double_upper I) (\<tau> \<sigma> i' - \<tau> \<sigma> x) \<or> memR (I) (\<tau> \<sigma> i' - \<tau> \<sigma> x)"
        by auto
      with 1 not_mem_I have "\<tau> \<sigma> i < \<tau> \<sigma> x"
        by (auto 0 3 elim: contrapos_np)
      then show ?case by (auto dest!: less_\<tau>D)
    qed
    then show ?thesis
      using P1 P2 \<open>i < i'\<close>
      by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) (auto simp: range_mapping_relax)
  next
    case False
   
    have future_bounded: "Formula.future_bounded (release_safe_bounded \<phi>1 I \<phi>2)"
      using 17(4)
      apply (auto simp add: release_safe_bounded_def)
      using False flip_int_less_lower_props memR_zero
      by blast
      
    show ?thesis using 17(3)[OF False future_bounded] False by auto
  qed
next
  case (18 I r)
  then show ?case
  proof (cases "regex.atms r = {}")
    case True
    with 18(2) show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"] exI[of _ i])
        (auto split: if_splits simp: pred_mapping_alt regex.pred_set)
  next
    case False
    define pick where "pick = (\<lambda>\<phi>. SOME Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) \<and>
       i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj))"
    let ?pickP = "fst o pick" let ?pickj = "snd o pick"
    from 18 have pick: "\<phi> \<in> regex.atms r \<Longrightarrow> dom (?pickP \<phi>) = S \<and>
      range_mapping i (?pickj \<phi>) (?pickP \<phi>) \<and> i \<le> progress \<sigma> (?pickP \<phi>) \<phi> (?pickj \<phi>)" for \<phi>
      unfolding pick_def o_def future_bounded.simps regex.pred_set
      by (intro someI_ex[where P = "\<lambda>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) \<and>
         i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)"]) auto
    with False show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "Max_mapping (?pickP ` regex.atms r)"] exI[of _ "Max (?pickj ` regex.atms r)"])
        (auto simp: Max_mapping_coboundedI
          order_trans[OF pick[THEN conjunct2, THEN conjunct2] progress_mono_gen])
  qed
next
  case (19 I r)
  from 19(2) obtain m where "\<not> memR I m"
    by (auto simp: bounded_memR)
  then obtain i' where "i < i'" and i': "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  have ix: "i \<le> x" if "memR I (\<tau> \<sigma> i' - \<tau> \<sigma> x)" for x
    using i' less_\<tau>D[of \<sigma> i x] that by (auto 0 3 simp: diff_le_mono2 elim: contrapos_np)
  show ?case
  proof (cases "regex.atms r = {}")
    case True
    with 19(2) ix show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some (Suc i') else None"] exI[of _ "Suc i'"])
        (auto split: if_splits simp: pred_mapping_alt regex.pred_set add.commute less_Suc_eq
          intro!: cInf_greatest dest!: spec[of _ i'] less_imp_le[THEN \<tau>_mono, of _ i' \<sigma>])
  next
    case False
    then obtain \<phi> where \<phi>: "\<phi> \<in> regex.atms r" by auto
    define pick where "pick = (\<lambda>\<phi>. SOME Pj. dom (fst Pj) = S \<and> range_mapping (Suc i') (snd Pj) (fst Pj) \<and>
      Suc i' \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj))"
    define pickP where "pickP = fst o pick" define pickj where "pickj = snd o pick"
    from 19 have pick: "\<phi> \<in> regex.atms r \<Longrightarrow> dom (pickP \<phi>) = S \<and>
    range_mapping (Suc i') (pickj \<phi>) (pickP \<phi>) \<and> Suc i' \<le> progress \<sigma> (pickP \<phi>) \<phi> (pickj \<phi>)" for \<phi>
      unfolding pick_def o_def future_bounded.simps regex.pred_set pickj_def pickP_def
      by (intro someI_ex[where P = "\<lambda>Pj. dom (fst Pj) = S \<and> range_mapping (Suc i') (snd Pj) (fst Pj) \<and>
       Suc i' \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)"]) auto
    let ?P = "Max_mapping (pickP ` regex.atms r)" let ?j = "Max (pickj ` regex.atms r)"
    from pick[OF \<phi>] False \<phi> have "Suc i' \<le> ?j"
      by (intro order_trans[OF pick[THEN conjunct2, THEN conjunct2], OF \<phi>] order_trans[OF progress_le_gen])
        (auto simp: Max_ge_iff dest: range_mapping_relax[of _ _ _ 0, OF _ _ order_refl, simplified])
    moreover
    note i' ix
    moreover
    from 19(2) have "Regex.pred_regex Formula.future_bounded r"
      by auto
    ultimately show ?thesis using \<tau>_mono[of _ ?j \<sigma>] less_\<tau>D[of \<sigma> i] pick False
      by (intro exI[of _ "?j"]  exI[of _ "?P"])
        (auto 0 3 intro!: cInf_greatest
          order_trans[OF le_SucI[OF order_refl] order_trans[OF pick[THEN conjunct2, THEN conjunct2] progress_mono_gen]]
          range_mapping_Max_mapping[OF _ _ ballI[OF range_mapping_relax[of "Suc i'" _ _ i, OF _ _ order_refl]]]
          simp: ac_simps Suc_le_eq trans_le_add2 Max_mapping_coboundedI progress_regex_def
          dest: spec[of _ "i'"] spec[of _ ?j])
  qed
qed (auto)


lemma progress_ge: "Formula.future_bounded \<phi> \<Longrightarrow> \<exists>j. i \<le> progress \<sigma> Map.empty \<phi> j"
  using progress_ge_gen[of \<phi> "{}" i \<sigma>]
  by auto

lemma cInf_restrict_nat:
  fixes x :: nat
  assumes "x \<in> A"
  shows "Inf A = Inf {y \<in> A. y \<le> x}"
  using assms by (auto intro!: antisym intro: cInf_greatest cInf_lower Inf_nat_def1)

lemma progress_time_conv:
  assumes "\<forall>i<j. \<tau> \<sigma> i = \<tau> \<sigma>' i"
  shows "progress \<sigma> P \<phi> j = progress \<sigma>' P \<phi> j"
  using assms
proof (induction P \<phi> j arbitrary: P rule: progress.induct[of _ \<sigma>])
  case (15 P \<phi> I \<psi> j)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with 15 show ?case
  proof (cases "bounded I")
    case True
    then show ?thesis
    proof (cases "j")
      case (Suc n)
      with * 15 show ?thesis
        using \<tau>_mono[THEN trans_le_add1]
        by (auto 6 0
            intro!: box_equals[OF arg_cong[where f=Inf]
              cInf_restrict_nat[symmetric, where x=n] cInf_restrict_nat[symmetric, where x=n]])
    qed simp
  qed (simp add: bounded_memR)
next
  case (17 P \<phi> I \<psi> j)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with 17 show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case mem: True
    show ?thesis
      using mem 17
    proof (cases "bounded I")
      case True
      then show ?thesis
        using mem
      proof (cases "j")
        case (Suc n)
        with * 17 show ?thesis
          using \<tau>_mono[THEN trans_le_add1] mem
          by (auto 6 0
              intro!: box_equals[OF arg_cong[where f=Inf]
                cInf_restrict_nat[symmetric, where x=n] cInf_restrict_nat[symmetric, where x=n]])
      qed simp
    qed (auto simp add: bounded_memR)
  next
    case False
    then show ?thesis using 17 by auto
  qed
next
  case (19 P I r j)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with 19 show ?case using \<tau>_mono[THEN trans_le_add1]
    by (cases "bounded I"; cases j)
      ((auto 6 0 simp: progress_le_gen progress_regex_def intro!: box_equals[OF arg_cong[where f=Inf]
            cInf_restrict_nat[symmetric, where x="j-1"] cInf_restrict_nat[symmetric, where x="j-1"]]) [])+
qed (auto simp: progress_regex_def)

lemma Inf_UNIV_nat: "(Inf UNIV :: nat) = 0"
  by (simp add: cInf_eq_minimum)

lemma progress_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "progress \<sigma> P \<phi> (plen \<pi>) = progress \<sigma>' P \<phi> (plen \<pi>)"
  using assms by (auto intro: progress_time_conv \<tau>_prefix_conv)

lemma bounded_rtranclp_mono:
  fixes n :: "'x :: linorder"
  assumes "\<And>i j. R i j \<Longrightarrow> j < n \<Longrightarrow> S i j" "\<And>i j. R i j \<Longrightarrow> i \<le> j"
  shows "rtranclp R i j \<Longrightarrow> j < n \<Longrightarrow> rtranclp S i j"
proof (induct rule: rtranclp_induct)
  case (step y z)
  then show ?case
    using assms(1,2)[of y z]
    by (auto elim!: rtrancl_into_rtrancl[to_pred, rotated])
qed auto



lemma sat_prefix_conv_gen:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "i < progress \<sigma> P \<phi> (plen \<pi>) \<Longrightarrow> dom V = dom V' \<Longrightarrow> dom P = dom V \<Longrightarrow>
    pred_mapping (\<lambda>x. x \<le> plen \<pi>) P \<Longrightarrow>
    (\<And>p i \<phi>. p \<in> dom V \<Longrightarrow> i < the (P p) \<Longrightarrow> the (V p) i = the (V' p) i) \<Longrightarrow>
    Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat \<sigma>' V' v i \<phi>"
proof (induction P \<phi> "(plen \<pi>)" arbitrary: V V' v i rule: progress.induct[of _ \<sigma>])
case (1 P e ts)
  from 1(1,4) have "i < plen \<pi>"
    by (blast intro!: order.strict_trans2 progress_le_gen)
  show ?case proof (cases "V e")
    case None
    then have "V' e = None" using \<open>dom V = dom V'\<close> by auto
    with None \<Gamma>_prefix_conv[OF assms(1,2) \<open>i < plen \<pi>\<close>] show ?thesis by simp
  next
    case (Some a)
    obtain a' where "V' e = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    then have "i < the (P e)"
      using 1(1-3) by (auto split: option.splits)
    then have "the (V e) i = the (V' e) i"
      using Some by (intro 1(5)) (simp_all add: domI)
    with Some \<open>V' e = Some a'\<close> show ?thesis by simp
  qed
next
  case (2 P p \<phi> \<psi>)
  let ?V = "\<lambda>V \<sigma>. (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>}))"
  show ?case unfolding sat.simps proof (rule 2(2))
    from 2 show "i < progress \<sigma> (P(p \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) \<psi> (plen \<pi>)"
      by simp
    from 2 show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by simp
    from 2 show "dom (P(p \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) = dom (?V V \<sigma>)"
      by simp
    from 2 show "pred_mapping (\<lambda>x. x \<le> plen \<pi>) (P(p \<mapsto> progress \<sigma> P \<phi> (plen \<pi>)))"
      by (auto intro!: pred_mapping_map_upd elim!: progress_le_gen)
  next
    fix p' i \<phi>'
    assume 1: "p' \<in> dom (?V V \<sigma>)" and 21: "i < the ((P(p \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) p')"
    show "the (?V V \<sigma> p') i = the (?V V' \<sigma>' p') i" proof (cases "p' = p")
      case True
      with 2 21 show ?thesis by auto
    next
      case False
      with 1 21 show ?thesis by (auto intro!: 2(7))
    qed
  qed
next
  case (9 P l)
  from 9(2-) have "\<forall>\<phi>\<in>set l. i < progress \<sigma> P \<phi> (plen \<pi>)"
    by (cases l) simp_all
  with 9 show ?case
    unfolding sat_Ands
    by fastforce
next
  case (12 P I \<phi>)
  with \<tau>_prefix_conv[OF assms(1,2)] show ?case
    by (cases i) (auto split: if_splits)
next
  case (13 P I \<phi>)
  then have "Suc i < plen \<pi>"
    by (auto intro: order.strict_trans2[OF _ progress_le_gen[of _ P \<sigma> \<phi>]])
  with 13 \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro conj_cong 13) auto
next
  case (14 P \<phi> I \<psi>)
   then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_le_gen])
  with 14 \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro conj_cong ex_cong ball_cong 14) auto
next
  case (15 P \<phi>1 I \<phi>2)
  from 15 have [simp]: "bounded I"
    by (cases "bounded I") (auto simp: bounded_memR Inf_UNIV_nat)
  from 15 obtain j where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    "j \<le> progress \<sigma> P \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma> P \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 1: "k < progress \<sigma> P \<phi>1 (plen \<pi>)" and 2: "k < progress \<sigma> P \<phi>2 (plen \<pi>)"
    if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
    using that
    by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
  have 3: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
    using 1[OF that] 15(6) by (auto simp only: less_eq_Suc_le order.trans[OF _ progress_le_gen])

  from 15 have "i < progress \<sigma>' P (Formula.Until \<phi>1 I \<phi>2) (plen \<pi>)"
    unfolding progress_prefix_conv[OF assms(1,2)] by simp
  then obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
    "j \<le> progress \<sigma>' P \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma>' P \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 11: "k < progress \<sigma> P \<phi>1 (plen \<pi>)" and 21: "k < progress \<sigma> P \<phi>2 (plen \<pi>)"
    if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    unfolding progress_prefix_conv[OF assms(1,2)]
    using that
    by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
  have 31: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    using 11[OF that] 15(6) by (auto simp only: less_eq_Suc_le order.trans[OF _ progress_le_gen])
  thm order.trans[OF _ progress_le_gen]

  show ?case unfolding sat.simps
  proof ((intro ex_cong iffI; elim conjE), goal_cases LR RL)
    case (LR j)
    with 15(1)[OF 1] 15(2)[OF 2] \<tau>_prefix_conv[OF assms(1,2) 3] 15(3-) show ?case
      by (auto 0 4 simp: le_diff_conv add.commute memR_antimono dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  next
    case (RL j)
    with 15(1)[OF 11] 15(2)[OF 21] \<tau>_prefix_conv[OF assms(1,2) 31] 15(3-) show ?case
      by (auto 0 4 simp: le_diff_conv add.commute memR_antimono dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  qed
next
  case (16 P \<phi> I \<psi>)
  then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_le_gen])
  then have "\<forall>j\<le>i. j < plen \<pi>"
    by auto
  then have t_eq: "\<forall>j\<le>i. \<tau> \<sigma> j = \<tau> \<sigma>' j"
    using \<tau>_prefix_conv[OF assms(1,2)]
    by auto

  have sat_subformulas:
    "\<forall>j\<le>i. Formula.sat \<sigma> V v j \<phi> = Formula.sat \<sigma>' V' v j \<phi>"    
    "\<forall>j\<le>i. Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma>' V' v j \<psi>"
    using 16(1-2)[OF _ 16(4,5,6,7)] 16(3)
    by auto

  show ?case
    using sat_subformulas t_eq
    by auto
next
  case (17 P \<phi> I \<psi>)

 have \<tau>_prefix_diff_conv: "\<And>k i. k < plen \<pi> \<Longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
  proof -
    fix k i
    assume assm: "k < plen \<pi>"
    {
      assume "i \<le> k"
      then have "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
        using assm \<tau>_prefix_conv[OF assms(1,2)]
        by auto
    }
    moreover {
      assume "i > k"
      then have
        "\<tau> \<sigma> k - \<tau> \<sigma> i = 0"
        "\<tau> \<sigma>' k - \<tau> \<sigma>' i = 0"
        by auto
      then have "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
        by auto
    }
    ultimately show "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" using not_le_imp_less by blast
  qed

  show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    have [simp]: "bounded (flip_int_double_upper I)"
      using True 17
      by (cases "bounded (flip_int_double_upper I)") (auto simp: bounded_memR Inf_UNIV_nat)
  
    define A where "A = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> min (progress \<sigma> P \<psi> (plen \<pi>)) (progress \<sigma> P \<phi> (plen \<pi>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    define B where "B = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> progress \<sigma> P \<psi> (plen \<pi>) \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  
    define A' where "A' = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> min (progress \<sigma>' P \<psi> (plen \<pi>)) (progress \<sigma>' P \<phi> (plen \<pi>)) \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
    define B' where "B' = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> progress \<sigma>' P \<psi> (plen \<pi>) \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
  
    have AA'_eq: "A = A'"
      using \<tau>_prefix_diff_conv
      unfolding A_def A'_def progress_prefix_conv[OF assms(1,2)]
      by auto
    have BB'_eq: "B = B'"
      using \<tau>_prefix_diff_conv
      unfolding B_def B'_def progress_prefix_conv[OF assms(1,2)]
      by auto
  
    have
      "(min (progress \<sigma> P \<psi> (plen \<pi>)) (progress \<sigma> P \<phi> (plen \<pi>))) \<in> A"
      "progress \<sigma> P \<psi> (plen \<pi>) \<in> B"
      unfolding A_def B_def
      by auto
    then have non_empty: 
      "A \<noteq> {}"
      "B \<noteq> {}"
      by auto
  
    have progress_eq: "progress \<sigma> P (formula.Release \<phi> I \<psi>) (plen \<pi>) = min (Inf A) (Inf B)"
      using min_Inf[OF non_empty] True
      unfolding A_def B_def
      by auto
  
    have "k < progress \<sigma> P \<phi> (plen \<pi>) \<and> k < progress \<sigma> P \<psi> (plen \<pi>)"
    if memR: "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
    proof (cases "progress \<sigma> P \<phi> (plen \<pi>) \<le> progress \<sigma> P \<psi> (plen \<pi>)")
      case assm: True
      show ?thesis
      proof (cases "Inf A \<le> Inf B")
        case True
        then have release_progress_eq: "progress \<sigma> P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf A"
          using progress_eq
          by auto
        then obtain j where
          "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          "j \<le> progress \<sigma> P \<phi> (plen \<pi>)"
          "j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
          using 17
          unfolding A_def
          by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
            dest!: le_cInf_iff[THEN iffD1, rotated -1])
        then show 1: "k < progress \<sigma> P \<phi> (plen \<pi>) \<and> k < progress \<sigma> P \<psi> (plen \<pi>)"
          using that
          by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
      next
        define J where "J = {j. \<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> j \<le> progress \<sigma> P \<psi> (plen \<pi>)}"
        define j where "j = Min J"
        case False
        then have release_progress_eq: "progress \<sigma> P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf B"
          using progress_eq
          by auto
        then obtain j' where
          "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma> j' - \<tau> \<sigma> i)"
          "j' \<le> progress \<sigma> P \<psi> (plen \<pi>)"
          using 17(5)
          unfolding B_def
          by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
            dest!: le_cInf_iff[THEN iffD1, rotated -1])
        then have "\<not> memR (I) (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "j' \<le> progress \<sigma> P \<psi> (plen \<pi>)"
          using memR_flip_int_double_upper
          by auto
        then have "j' \<in> J"
          unfolding J_def
          by auto
        then have J_props: "J \<noteq> {}" "finite J"
          unfolding J_def
          by auto
        then have "j \<in> J"
          unfolding j_def
          by auto
        then have j_props: "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
          unfolding J_def
          by auto
        have less_j_mem: "\<And>l. l<j \<Longrightarrow> memR I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
        proof -
          fix l
          assume l_j: "l < j"
          {
            assume "\<not>memR I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
            then have "l \<in> J"
              using l_j j_props(2)
              unfolding J_def
              by auto
            then have "False"
              using l_j J_props
              unfolding j_def
              by auto
          }
          then show "memR I (\<tau> \<sigma> l - \<tau> \<sigma> i)" by auto
        qed
        have j_leq: "j \<le> progress \<sigma> P \<phi> (plen \<pi>)"
        proof -
          {
            assume j_g: "j > progress \<sigma> P \<phi> (plen \<pi>)"
            have "\<And>k. k < plen \<pi> \<Longrightarrow> k \<le> min (Monitor.progress \<sigma> P \<psi> (plen \<pi>)) (Monitor.progress \<sigma> P \<phi> (plen \<pi>)) \<Longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
            proof -
              fix k
              assume "k < plen \<pi>" "k \<le> min (Monitor.progress \<sigma> P \<psi> (plen \<pi>)) (Monitor.progress \<sigma> P \<phi> (plen \<pi>))"
              then have "k < j" using j_g
                by auto
              then show "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
                using less_j_mem
                by auto
            qed
            then have "i \<in> A"
              unfolding A_def
              by auto
            then have "i \<ge> Inf A"
              by (simp add: cInf_lower)
            moreover have "i < Inf A"
              using 17(5) release_progress_eq False
              by auto
            ultimately have "False"
              by auto
          }
          then show ?thesis using not_le_imp_less by auto
        qed
        then show "k < progress \<sigma> P \<phi> (plen \<pi>) \<and> k < progress \<sigma> P \<psi> (plen \<pi>)"
          using that j_props
          by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
      qed
    next
      case assm: False
      then have A_eq: "A = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> (Monitor.progress \<sigma> P \<psi> (plen \<pi>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
        unfolding A_def
        by auto
      have "A \<subseteq> B"
      proof -
        {
          fix i
          assume "i \<in> A"
          then have i_props: "\<forall>k. k < (plen \<pi>) \<and> k \<le> Monitor.progress \<sigma> P \<psi> (plen \<pi>) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
            unfolding A_eq
            by auto
          then have "\<And>k. k < (plen \<pi>) \<and> k \<le> Monitor.progress \<sigma> P \<psi> (plen \<pi>) \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)"
            using memR_flip_int_double_upper not_le_imp_less
            by auto
          then have "i \<in> B"
            unfolding B_def
            by auto
        }
        then show ?thesis by blast
      qed
      then have "Inf B \<le> Inf A"
        using Inf_leq[OF non_empty(1), of B]
        by auto
      then have release_progress_eq: "progress \<sigma> P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf B"
        using progress_eq
        by auto
      then have "\<exists>j. \<not> memR (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
        using 17
        unfolding B_def
        by (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
          dest!: le_cInf_iff[THEN iffD1, rotated -1])
      then obtain j where
        "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        "j \<le> progress \<sigma> P \<phi> (plen \<pi>)"
        "j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
        using assm
        by auto
      then have 1: "k < progress \<sigma> P \<phi> (plen \<pi>)" and 2: "k < progress \<sigma> P \<psi> (plen \<pi>)"
        if "memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
        using that
        by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
      then show ?thesis
        using memR_flip_int_double_upper memR
        by auto
    qed
    then have 1: "k < progress \<sigma> P \<phi> (plen \<pi>)" and 2: "k < progress \<sigma> P \<psi> (plen \<pi>)"
      if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using that
      by auto
  
    have "k < progress \<sigma>' P \<phi> (plen \<pi>) \<and> k < progress \<sigma>' P \<psi> (plen \<pi>)"
    if memR: "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    proof (cases "progress \<sigma> P \<phi> (plen \<pi>) \<le> progress \<sigma> P \<psi> (plen \<pi>)")
      case assm: True
      show ?thesis
      proof (cases "Inf A \<le> Inf B")
        case True
        then have release_progress_eq: "progress \<sigma>' P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf A'"
          using progress_eq AA'_eq
          unfolding progress_prefix_conv[OF assms(1,2)]
          by auto
        then obtain j where
          "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
          "j \<le> progress \<sigma>' P \<phi> (plen \<pi>)"
          "j \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
          using 17(5)
          unfolding A'_def progress_prefix_conv[OF assms(1,2)]
          by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
            dest!: le_cInf_iff[THEN iffD1, rotated -1])
        then show 1: "k < progress \<sigma>' P \<phi> (plen \<pi>) \<and> k < progress \<sigma>' P \<psi> (plen \<pi>)"
          using that
          by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
      next
        define J where "J = {j. \<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<and> j \<le> progress \<sigma>' P \<psi> (plen \<pi>)}"
        define j where "j = Min J"
        case False
        then have release_progress_eq: "progress \<sigma>' P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf B'"
          using progress_eq BB'_eq
          unfolding progress_prefix_conv[OF assms(1,2)]
          by auto
        then obtain j' where
          "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma>' j' - \<tau> \<sigma>' i)"
          "j' \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
          using 17(5)
          unfolding B'_def progress_prefix_conv[OF assms(1,2)]
          by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
            dest!: le_cInf_iff[THEN iffD1, rotated -1])
        then have "\<not> memR (I) (\<tau> \<sigma>' j' - \<tau> \<sigma>' i)" "j' \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
          using memR_flip_int_double_upper
          by auto
        then have "j' \<in> J"
          unfolding J_def
          by auto
        then have J_props: "J \<noteq> {}" "finite J"
          unfolding J_def
          by auto
        then have "j \<in> J"
          unfolding j_def
          by auto
        then have j_props: "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" "j \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
          unfolding J_def
          by auto
        have less_j_mem: "\<And>l. l<j \<Longrightarrow> memR I (\<tau> \<sigma>' l - \<tau> \<sigma>' i)"
        proof -
          fix l
          assume l_j: "l < j"
          {
            assume "\<not>memR I (\<tau> \<sigma>' l - \<tau> \<sigma>' i)"
            then have "l \<in> J"
              using l_j j_props(2)
              unfolding J_def
              by auto
            then have "False"
              using l_j J_props
              unfolding j_def
              by auto
          }
          then show "memR I (\<tau> \<sigma>' l - \<tau> \<sigma>' i)" by auto
        qed
        have j_leq: "j \<le> progress \<sigma>' P \<phi> (plen \<pi>)"
        proof -
          {
            assume j_g: "j > progress \<sigma>' P \<phi> (plen \<pi>)"
            have "\<And>k. k < plen \<pi> \<Longrightarrow> k \<le> min (Monitor.progress \<sigma>' P \<psi> (plen \<pi>)) (Monitor.progress \<sigma>' P \<phi> (plen \<pi>)) \<Longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
            proof -
              fix k
              assume "k < plen \<pi>" "k \<le> min (Monitor.progress \<sigma>' P \<psi> (plen \<pi>)) (Monitor.progress \<sigma>' P \<phi> (plen \<pi>))"
              then have "k < j" using j_g
                by auto
              then show "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
                using less_j_mem
                by auto
            qed
            then have "i \<in> A'"
              unfolding A'_def
              by auto
            then have "i \<ge> Inf A'"
              by (simp add: cInf_lower)
            moreover have "i < Inf A'"
              using 17(5) release_progress_eq False
              unfolding AA'_eq BB'_eq progress_prefix_conv[OF assms(1,2)]
              by auto
            ultimately have "False"
              by auto
          }
          then show ?thesis using not_le_imp_less by auto
        qed
        then show "k < progress \<sigma>' P \<phi> (plen \<pi>) \<and> k < progress \<sigma>' P \<psi> (plen \<pi>)"
          using that j_props
          by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
      qed
    next
      case assm: False
      then have A'_eq: "A' = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> (Monitor.progress \<sigma>' P \<psi> (plen \<pi>)) \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
        unfolding A'_def progress_prefix_conv[OF assms(1,2)]
        by auto
      have "A' \<subseteq> B'"
      proof -
        {
          fix i
          assume "i \<in> A'"
          then have i_props: "\<forall>k. k < (plen \<pi>) \<and> k \<le> Monitor.progress \<sigma>' P \<psi> (plen \<pi>) \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
            unfolding A'_eq
            by auto
          then have "\<And>k. k < (plen \<pi>) \<and> k \<le> Monitor.progress \<sigma>' P \<psi> (plen \<pi>) \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
            using memR_flip_int_double_upper not_le_imp_less
            by auto
          then have "i \<in> B'"
            unfolding B'_def
            by auto
        }
        then show ?thesis by blast
      qed
      then have "Inf B' \<le> Inf A'"
        using Inf_leq[OF non_empty(1), of B'] BB'_eq AA'_eq
        by auto
      then have release_progress_eq: "progress \<sigma>' P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf B'"
        using progress_eq BB'_eq AA'_eq
        unfolding progress_prefix_conv[OF assms(1,2)]
        by auto
      then have "\<exists>j. \<not> memR (flip_int_double_upper I) (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<and> j \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
        using 17(5)
        unfolding B'_def progress_prefix_conv[OF assms(1,2)]
        by (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
          dest!: le_cInf_iff[THEN iffD1, rotated -1])
      then obtain j where
        "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        "j \<le> progress \<sigma>' P \<phi> (plen \<pi>)"
        "j \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
        using assm
        unfolding progress_prefix_conv[OF assms(1,2)]
        by auto
      then have 1: "k < progress \<sigma>' P \<phi> (plen \<pi>)" and 2: "k < progress \<sigma>' P \<psi> (plen \<pi>)"
        if "memR (flip_int_double_upper I) (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
        using that
        by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
      then show ?thesis
        using memR_flip_int_double_upper memR
        by auto
    qed
    then have 11: "k < progress \<sigma>' P \<phi> (plen \<pi>)" and 21: "k < progress \<sigma>' P \<psi> (plen \<pi>)"
      if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using that
      by auto
  
    have 3: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using 1[OF that] 17(8) by (auto simp only: less_eq_Suc_le order.trans[OF _ progress_le_gen])
    have 31: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using 11[OF that] 17(8) by (auto simp only: less_eq_Suc_le order.trans[OF _ progress_le_gen])
  
    have t_eq1: "\<And>j. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> \<tau> \<sigma> j = \<tau> \<sigma>' j"
      using \<tau>_prefix_conv[OF assms(1,2) 3] memR_flip_int_double_upper
      by auto
  
    have t_eq2: "\<And>j. memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<Longrightarrow> \<tau> \<sigma> j = \<tau> \<sigma>' j"
      using \<tau>_prefix_conv[OF assms(1,2) 31] memR_flip_int_double_upper
      by auto
    
    have sat_subformulas:
      "\<And>j v. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> Formula.sat \<sigma> V v j \<phi> = Formula.sat \<sigma>' V' v j \<phi>"
      "\<And>j v. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma>' V' v j \<psi>"
      using 17(2)[OF True 1 17(6-9)] 17(1)[OF True 2 17(6-9)] 17(5) memR_flip_int_double_upper
      by auto
  
    have "\<And>j k. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> k \<le> j \<Longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      using memR_antimono[of I]
      using \<tau>_mono diff_le_mono
      by blast
    then have "\<And>j k. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> k \<le> j \<Longrightarrow> Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma>' V' v k \<phi>"
      using sat_subformulas(1)
      by auto
  
    then have release_eq: "\<And>j. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (
        (Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)) =
        (Formula.sat \<sigma>' V' v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma>' V' v k \<phi>))
    )"
      using sat_subformulas(2)
      by auto
    
    show ?thesis
    proof (rule iffI)
      assume assm: "Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>)"
      {
        fix j
        assume assms: "j \<ge> i" "mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        then have memR: "memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" by auto
        have memRi: "memR I (\<tau> \<sigma>' i - \<tau> \<sigma>' i)" by auto
        have mem: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          using assms(2)[unfolded t_eq2[OF memR,symmetric] t_eq2[OF memRi,symmetric]]
          by auto
        have sat: "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using assm assms(1) mem
          by auto
        then have "Formula.sat \<sigma>' V' v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma>' V' v k \<phi>)"
          using mem release_eq[of j]
          by auto
      }
      then show "Formula.sat \<sigma>' V' v i (formula.Release \<phi> I \<psi>)"
        by auto
    next
      assume assm: "Formula.sat \<sigma>' V' v i (formula.Release \<phi> I \<psi>)"
      {
        fix j
        assume assms: "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        then have memR: "memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" by auto
        have memRi: "memR I (\<tau> \<sigma> i - \<tau> \<sigma> i)" by auto
        have mem: "mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
          using assms(2)[unfolded t_eq1[OF memR] t_eq1[OF memRi]]
          by auto
        have sat: "Formula.sat \<sigma>' V' v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma>' V' v k \<phi>)"
          using assm assms(1) mem
          by auto
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using assms(2) release_eq[of j]
          by auto
      }
      then show "Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>)"
        by auto
    qed
  next
    case False
    then have i_le: "i < Monitor.progress \<sigma> P (release_safe_bounded \<phi> I \<psi>) (plen \<pi>)"
      using 17(5)
      by auto

    have rewrite_conds: "bounded I" "\<not> mem I 0"
      using False
      by auto
    
    have sat_safe_bounded_eq: "\<And>v.
        Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I \<psi>) = Formula.sat \<sigma>' V' v i (release_safe_bounded \<phi> I \<psi>)"
      using 17(4)[OF False i_le 17(6-9)] 17(5)
      by auto

    show ?thesis
    proof (cases "\<exists>j\<in>{i..<plen \<pi>}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)")
      case True
      then have "\<exists>j\<in>{i..<plen \<pi>}. mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using \<tau>_prefix_diff_conv
        by auto
      then have
        "Formula.sat \<sigma> V v i (Formula.eventually I Formula.TT)"
        "Formula.sat \<sigma>' V' v i (Formula.eventually I Formula.TT)"
        using True
        by auto
      then have r:
        "Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I \<psi>)"
        "Formula.sat \<sigma>' V' v i (formula.Release \<phi> I \<psi>) = Formula.sat \<sigma>' V' v i (release_safe_bounded \<phi> I \<psi>)"
        using sat_release_rewrite[OF rewrite_conds, of _ _ v i \<phi> \<psi>]
        by auto
      
      show ?thesis
        using sat_safe_bounded_eq[of v]
        unfolding r
        by blast
    next
      case int_props: False
      then have int_props:
        "\<forall>j\<in>{i..<plen \<pi>}. \<not>mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        "\<forall>j\<in>{i..<plen \<pi>}. \<not>mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using \<tau>_prefix_diff_conv
        by auto

      have "i < progress \<sigma> P (release_safe_bounded \<phi> I \<psi>) (plen \<pi>)"
        using False 17(5)
        by auto
      then have i_le: "i < progress \<sigma> P (Formula.eventually I Formula.TT) (plen \<pi>)"
        unfolding release_safe_bounded_def
        by auto
      moreover have
        "progress \<sigma> P (Formula.eventually I Formula.TT) (plen \<pi>) =
        progress \<sigma>' P (Formula.eventually I Formula.TT) (plen \<pi>)"
        by (meson assms(1) assms(2) progress_prefix_conv)
      ultimately have i_le': "i < progress \<sigma>' P (Formula.eventually I Formula.TT) (plen \<pi>)"
        by auto

      have "\<And>j. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> j < plen \<pi>"
      proof -
        fix j
        assume mem: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        {
          assume assm: "j \<ge> plen \<pi>"
          have "{i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} = {i. \<forall>k. k < plen \<pi> \<and> k \<le> plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
            by auto
          have "\<And>k. k < plen \<pi> \<Longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
          proof -
            fix k
            assume "k < plen \<pi>"
            then have "k < j"
              using assm
              by auto
            then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j"
              by auto
            then show "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
              using mem
              by auto
          qed
          then have "i \<in> {i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
            by auto
          then have "i \<ge> progress \<sigma> P (Formula.eventually I Formula.TT) (plen \<pi>)"
            unfolding progress_eventually progress_TT
            by (auto simp add: cInf_lower)
          then have "False"
            using i_le
            by auto
        }
        then show "j < plen \<pi>"
          using not_le
          by blast
      qed
      then have "\<forall>j\<ge>plen \<pi>. \<not>mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        using leD
        by blast
      then have not_mem_\<sigma>: "\<forall>j\<ge>i. \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        using int_props
        by auto

      have "\<And>j. mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<Longrightarrow> j < plen \<pi>"
      proof -
        fix j
        assume mem: "mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        {
          assume assm: "j \<ge> plen \<pi>"
          have "{i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)} = {i. \<forall>k. k < plen \<pi> \<and> k \<le> plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
            by auto
          have "\<And>k. k < plen \<pi> \<Longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
          proof -
            fix k
            assume "k < plen \<pi>"
            then have "k < j"
              using assm
              by auto
            then have "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' j"
              by auto
            then show "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
              using mem
              by auto
          qed
          then have "i \<in> {i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
            by auto
          then have "i \<ge> progress \<sigma>' P (Formula.eventually I Formula.TT) (plen \<pi>)"
            unfolding progress_eventually progress_TT
            by (auto simp add: cInf_lower)
          then have "False"
            using i_le'
            by auto
        }
        then show "j < plen \<pi>"
          using not_le
          by blast
      qed
      then have "\<forall>j\<ge>plen \<pi>. \<not>mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using leD
        by blast
      then have not_mem_\<sigma>': "\<forall>j\<ge>i. \<not> mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using int_props
        by auto

      show ?thesis
        using not_mem_\<sigma> not_mem_\<sigma>'
        by auto
    qed
  qed
next
  case (18 P I r)
  then have "i < plen \<pi>"
    by (force simp: pred_mapping_alt elim!: order.strict_trans2[OF _ progress_le_gen])
  with 18 \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro ex_cong conj_cong match_cong_strong 18) (auto simp: progress_regex_def split: if_splits)
next
  case (19 P I r)
  from 19 have [simp]: "bounded I"
    by (cases "bounded I") (auto simp: bounded_memR Inf_UNIV_nat)
  show ?case
  proof (cases "regex.atms r = {}")
    case True
    from 19 obtain j where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "j \<le> plen \<pi>"
      by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 1: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      by (meson \<tau>_mono diff_le_mono memR_antimono not_le_imp_less that)
    from 19 have "i < progress \<sigma>' P (Formula.MatchF I r) (plen \<pi>)"
      unfolding progress_prefix_conv[OF assms(1,2)] by blast
    then obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" "j \<le> plen \<pi>"
      by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 2: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      by (meson \<tau>_mono diff_le_mono memR_antimono not_le_imp_less that)
    from 19 True show ?thesis
      unfolding sat.simps conj_commute[of "memL _ _"]
    proof (intro ex_cong conj_cong match_cong_strong, goal_cases memL memR sat)
      case (memL j)
      then show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 1, symmetric]; auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2]; auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (memR j)
      then show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2, symmetric]; auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2]; auto elim: order.trans[OF \<tau>_mono, rotated]))
    qed auto
  next
    case False
    from 19 False obtain j where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "(\<forall>x\<in>regex.atms r. j \<le> progress \<sigma> P x (plen \<pi>))"
      by atomize_elim (auto 0 6 simp add: less_eq_Suc_le not_le progress_regex_def
        dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 1: "\<phi> \<in> regex.atms r \<Longrightarrow> k < progress \<sigma> P \<phi> (plen \<pi>)" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k \<phi>
      using that
      by (auto 0 3 elim!: contrapos_np[of _ "_ < _"] simp: diff_le_mono)
    then have 2: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "regex.atms r \<noteq> {}" for k
      using that
      by (fastforce intro: order.strict_trans2[OF _ progress_le_gen[OF 19(5), of \<sigma>], of k])

    from 19 have "i < progress \<sigma>' P (Formula.MatchF I r) (plen \<pi>)"
      unfolding progress_prefix_conv[OF assms(1,2)] by blast
    with False obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" "(\<forall>x\<in>regex.atms r. j \<le> progress \<sigma>' P x (plen \<pi>))"
      by atomize_elim (auto 0 6 simp add: less_eq_Suc_le not_le progress_regex_def
        dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 11:  "\<phi> \<in> regex.atms r \<Longrightarrow> k < progress \<sigma> P \<phi> (plen \<pi>)" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k \<phi>
      using that using progress_prefix_conv[OF assms(1,2)]
      by (auto 0 3 elim!: contrapos_np[of _ "_ < _"] simp: diff_le_mono)
    have 21: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using 11[OF that(1)] False by (fastforce intro: order.strict_trans2[OF _ progress_le_gen[OF 19(5), of \<sigma>], of k])
 
    
    show ?thesis unfolding sat.simps conj_commute[of "memL _ _"]
    proof ((intro ex_cong conj_cong match_cong_strong 19(1)[OF False _ _ 19(3-6)]; assumption?), goal_cases memR memL progress)
      case (memR j)
      with False show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2, symmetric]; auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (memL j)
      with False show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21, symmetric]; auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (progress j k z)
      with False show ?case
        by (elim 1[rotated])
          (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; auto simp: diff_le_mono memR_antimono elim!: contrapos_np[of _ False])
    qed
  qed
qed (auto)

lemma sat_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "i < progress \<sigma> Map.empty \<phi> (plen \<pi>) \<Longrightarrow>
    Formula.sat \<sigma> Map.empty v i \<phi> \<longleftrightarrow> Formula.sat \<sigma>' Map.empty v i \<phi>"
  by (erule sat_prefix_conv_gen[OF assms]) auto

lemma progress_remove_neg[simp]: "progress \<sigma> P (remove_neg \<phi>) j = progress \<sigma> P \<phi> j"
  by (cases \<phi>) simp_all

lemma safe_progress_get_and: "safe_formula \<phi> \<Longrightarrow>
  Min ((\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` set (get_and_list \<phi>)) = progress \<sigma> P \<phi> j"
  by (induction \<phi> rule: get_and_list.induct) auto

lemma progress_convert_multiway: "safe_formula \<phi> \<Longrightarrow> progress \<sigma> P (convert_multiway \<phi>) j = progress \<sigma> P \<phi> j"
proof (induction \<phi> arbitrary: P rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?c = "convert_multiway (Formula.And \<phi> \<psi>)"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have c_eq: "?c = Formula.Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  from \<open>safe_formula \<phi>\<close> have "safe_formula ?c\<phi>" by (rule safe_convert_multiway)
  moreover from \<open>safe_formula \<psi>\<close> have "safe_formula ?c\<psi>" by (rule safe_convert_multiway)
  ultimately show ?case
    unfolding c_eq
    using And_safe.IH
    by (auto simp: get_and_nonempty Min.union safe_progress_get_and)
next
  case (And_Not \<phi> \<psi>)
  let ?c = "convert_multiway (Formula.And \<phi> (Formula.Neg \<psi>))"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have c_eq: "?c = Formula.Ands (Formula.Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  from \<open>safe_formula \<phi>\<close> have "safe_formula ?c\<phi>" by (rule safe_convert_multiway)
  moreover from \<open>safe_formula \<psi>\<close> have "safe_formula ?c\<psi>" by (rule safe_convert_multiway)
  ultimately show ?case
    unfolding c_eq
    using And_Not.IH
    by (auto simp: get_and_nonempty Min.union safe_progress_get_and)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Formula.Trigger \<phi>' I \<psi>'"
  define f where "f = Formula.And \<phi> t"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have t_prog: "progress \<sigma> P (convert_multiway t) j = progress \<sigma> P t j"
    using And_Trigger(6-7)[of P]
    unfolding t_def
    by auto

  show ?case
  proof (cases "safe_formula t")
  case True
    then obtain l where l_props:
      "convert_multiway f = Formula.Ands l"
      "set l = set (get_and_list (convert_multiway \<phi>)) \<union> {convert_multiway t}"
      using t_not_safe_assign t_not_constraint And_Trigger(3)
      unfolding f_def t_def
      by (auto simp add: safe_formula_dual_def split: if_splits)
  
    moreover have "progress \<sigma> P f j = Min (set (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) l))"
      using l_props(2) And_Trigger(5)[of P] t_prog safe_convert_multiway[OF And_Trigger(1)]
      unfolding f_def
    by (cases "convert_multiway \<phi>") (auto split: if_splits)
  
    ultimately show ?thesis 
      unfolding f_def t_def
      by auto
  next
    case False
    then have convert_f: "convert_multiway f = Formula.And (convert_multiway \<phi>) (Formula.Trigger (convert_multiway \<phi>') I (convert_multiway \<psi>'))"
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
  then show ?case using progress_and_release_rewrite_bounded by auto
next
  case (Ands l pos neg)
  then have l_future_bounded: "list_all (\<lambda>a. progress \<sigma> P (convert_multiway a) j = Monitor.progress \<sigma> P a j) l"
  proof -
    {
      fix \<phi>
      assume assm: "\<phi> \<in> set l"
      then have "progress \<sigma> P (convert_multiway \<phi>) j = Monitor.progress \<sigma> P \<phi> j"
      proof (cases "\<phi> \<in> set pos")
        case True
        then show ?thesis using Ands(6) by (auto simp add: list_all_iff)
      next
        case False
        then have \<phi>'_props: "case \<phi> of Formula.Neg \<phi>' \<Rightarrow> \<forall>P. progress \<sigma> P (convert_multiway \<phi>') j = progress \<sigma> P \<phi>' j
           | _ \<Rightarrow> (\<forall>P. progress \<sigma> P (convert_multiway \<phi>) j = progress \<sigma> P \<phi> j)"
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
  case (Trigger_0 \<phi> I \<psi>)
  show ?case
  proof (cases "safe_assignment (fv \<psi>) \<phi> \<or> is_constraint \<phi> \<or> (case \<phi> of formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> (\<forall>x. Monitor.progress \<sigma> x (convert_multiway \<phi>') j = Monitor.progress \<sigma> x \<phi>' j) | _ \<Rightarrow> False)")
    case True
    moreover {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis
        unfolding safe_assignment_def
        using Trigger_0
        by (cases \<phi>) (auto)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
        using Trigger_0
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using Trigger_0 assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> (\<forall>x. Monitor.progress \<sigma> x (convert_multiway \<phi>') j = Monitor.progress \<sigma> x \<phi>' j) | _ \<Rightarrow> False)"
      then obtain \<phi>' where \<phi>'_props:
        "\<phi> = formula.Neg \<phi>'"
        "safe_formula \<phi>'"
        "\<forall>x. Monitor.progress \<sigma> x (convert_multiway \<phi>') j = Monitor.progress \<sigma> x \<phi>' j"
        by (auto split: formula.splits)
      then have ?thesis using Trigger_0 by auto
    }
    ultimately show ?thesis by blast
  next
    case False
    then show ?thesis using Trigger_0 by (cases \<phi>) (auto)
  qed
next
  case (Release_0 \<phi> I \<psi>)
  then show ?case using progress_release_rewrite_0 by auto
next
  case (MatchP I r)
  from MatchP show ?case
    unfolding progress.simps regex.map convert_multiway.simps regex.set_map image_image
    by (intro if_cong arg_cong[of _ _ Min] image_cong)
      (auto 0 4 simp: atms_def elim!: disjE_Not2 dest: safe_regex_safe_formula)
next
  case (MatchF I r)
  from MatchF show ?case
    unfolding progress.simps regex.map convert_multiway.simps regex.set_map image_image
    by (intro if_cong arg_cong[of _ _ Min] arg_cong[of _ _ Inf] arg_cong[of _ _ "(\<le>) _"]
      image_cong Collect_cong all_cong1 imp_cong conj_cong image_cong)
      (auto 0 4 simp: atms_def elim!: disjE_Not2 dest: safe_regex_safe_formula)
qed (auto)


subsection \<open>Specification\<close>

definition pprogress :: "Formula.formula \<Rightarrow> Formula.prefix \<Rightarrow> nat" where
  "pprogress \<phi> \<pi> = (THE n. \<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> progress \<sigma> Map.empty \<phi> (plen \<pi>) = n)"

lemma pprogress_eq: "prefix_of \<pi> \<sigma> \<Longrightarrow> pprogress \<phi> \<pi> = progress \<sigma> Map.empty \<phi> (plen \<pi>)"
  unfolding pprogress_def using progress_prefix_conv
  by blast

locale future_bounded_mfodl =
  fixes \<phi> :: Formula.formula
  assumes future_bounded: "Formula.future_bounded \<phi>"

sublocale future_bounded_mfodl \<subseteq> sliceable_timed_progress "Formula.nfv \<phi>" "Formula.fv \<phi>" "relevant_events \<phi>"
  "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" "pprogress \<phi>"
proof (unfold_locales, goal_cases)
  case (1 x)
  then show ?case by (simp add: fvi_less_nfv)
next
  case (2 v v' \<sigma> i)
  then show ?case by (simp cong: sat_fv_cong[rule_format])
next
  case (3 v S \<sigma> i)
  then show ?case
    using sat_slice_iff[symmetric] by simp
next
  case (4 \<pi> \<pi>')
  moreover obtain \<sigma> where "prefix_of \<pi>' \<sigma>"
    using ex_prefix_of ..
  moreover have "prefix_of \<pi> \<sigma>"
    using prefix_of_antimono[OF \<open>\<pi> \<le> \<pi>'\<close> \<open>prefix_of \<pi>' \<sigma>\<close>] .
  ultimately show ?case
    by (simp add: pprogress_eq plen_mono progress_mono)
next
  case (5 \<sigma> x)
  obtain j where "x \<le> progress \<sigma> Map.empty \<phi> j"
    using future_bounded progress_ge by blast
  then have "x \<le> pprogress \<phi> (take_prefix j \<sigma>)"
    by (simp add: pprogress_eq[of _ \<sigma>])
  then show ?case by force
next
  case (6 \<pi> \<sigma> \<sigma>' i v)
  then have "i < progress \<sigma> Map.empty \<phi> (plen \<pi>)"
    by (simp add: pprogress_eq)
  with 6 show ?case
    using sat_prefix_conv by blast
next
  case (7 \<pi> \<pi>')
  then have "plen \<pi> = plen \<pi>'"
    by transfer (simp add: list_eq_iff_nth_eq)
  moreover obtain \<sigma> \<sigma>' where "prefix_of \<pi> \<sigma>" "prefix_of \<pi>' \<sigma>'"
    using ex_prefix_of by blast+
  moreover have "\<forall>i < plen \<pi>. \<tau> \<sigma> i = \<tau> \<sigma>' i"
    using 7 calculation
    by transfer (simp add: list_eq_iff_nth_eq)
  ultimately show ?case
    by (simp add: pprogress_eq progress_time_conv)
qed

locale verimon_spec =
  fixes \<phi> :: Formula.formula
  assumes monitorable: "mmonitorable \<phi>"

sublocale verimon_spec \<subseteq> future_bounded_mfodl
  using monitorable by unfold_locales (simp add: mmonitorable_def)


subsection \<open>Correctness\<close>

subsubsection \<open>Invariants\<close>

definition wf_mbuf2 where
  "wf_mbuf2 i ja jb P Q buf \<longleftrightarrow> i \<le> ja \<and> i \<le> jb \<and> (case buf of (xs, ys) \<Rightarrow>
    list_all2 P [i..<ja] xs \<and> list_all2 Q [i..<jb] ys)"

inductive list_all3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool" for P :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool)" where
  "list_all3 P [] [] []"
| "P a1 a2 a3 \<Longrightarrow> list_all3 P q1 q2 q3 \<Longrightarrow> list_all3 P (a1 # q1) (a2 # q2) (a3 # q3)"

lemma list_all3_list_all2D: "list_all3 P xs ys zs \<Longrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  by (induct xs ys zs rule: list_all3.induct) auto

lemma list_all2_list_all3I: "length xs = length ys \<Longrightarrow> list_all2 (case_prod P) (zip xs ys) zs \<Longrightarrow>
  list_all3 P xs ys zs"
  by (induct xs ys arbitrary: zs rule: list_induct2)
    (auto simp: list_all2_Cons1 intro: list_all3.intros)

lemma list_all3_list_all2_eq: "list_all3 P xs ys zs \<longleftrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  using list_all2_list_all3I list_all3_list_all2D by blast

lemma list_all3_mapD: "list_all3 P (map f xs) (map g ys) (map h zs) \<Longrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  by (induct "map f xs" "map g ys" "map h zs" arbitrary: xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_mapI: "list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs \<Longrightarrow>
  list_all3 P (map f xs) (map g ys) (map h zs)"
  by (induct xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_map_iff: "list_all3 P (map f xs) (map g ys) (map h zs) \<longleftrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  using list_all3_mapD list_all3_mapI by blast

lemmas list_all3_map =
  list_all3_map_iff[where g=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and g=id, unfolded list.map_id id_apply]

lemma list_all3_conv_all_nth:
  "list_all3 P xs ys zs =
  (length xs = length ys \<and> length ys = length zs \<and> (\<forall>i < length xs. P (xs!i) (ys!i) (zs!i)))"
  by (auto simp add: list_all3_list_all2_eq list_all2_conv_all_nth)

lemma list_all3_refl [intro?]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x x x) \<Longrightarrow> list_all3 P xs xs xs"
  by (simp add: list_all3_conv_all_nth)

definition wf_mbufn :: "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> event_data table \<Rightarrow> bool) list \<Rightarrow> event_data mbufn \<Rightarrow> bool" where
  "wf_mbufn i js Ps buf \<longleftrightarrow> list_all3 (\<lambda>P j xs. i \<le> j \<and> list_all2 P [i..<j] xs) Ps js buf"

definition wf_mbuf2' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
  Formula.formula \<Rightarrow> Formula.formula \<Rightarrow> event_data mbuf2 \<Rightarrow> bool" where
  "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf \<longleftrightarrow> wf_mbuf2 (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j))
    (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)
    (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
    (\<lambda>i (r). qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r) buf"

definition wf_dfvs where "
  wf_dfvs dfvs \<sigma> I i \<phi> = (if (\<forall>j\<le>i. \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)) then
    dfvs = {}
  else
    dfvs = fv \<phi>
  )"

definition wf_mbuft2' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
  Formula.formula \<Rightarrow> Formula.formula \<Rightarrow> \<I> \<Rightarrow> Formula.formula \<Rightarrow> event_data mbuft2 \<Rightarrow> bool" where
  "wf_mbuft2' \<sigma> P V j n R \<phi> \<alpha> I \<beta> buf \<longleftrightarrow> wf_mbuf2 (min (progress \<sigma> P \<phi> j) (progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j))
    (progress \<sigma> P \<phi> j) (progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)
    (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
    (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r) buf"


definition wf_mbufn' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
  Formula.formula Regex.regex \<Rightarrow> event_data mbufn \<Rightarrow> bool" where
  "wf_mbufn' \<sigma>  P V j n R r buf \<longleftrightarrow> (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
    wf_mbufn (progress_regex \<sigma> P r j) (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s)
    (map (\<lambda>\<phi> i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r) \<phi>s)
    buf)"

lemma wf_mbuf2'_UNIV_alt: "wf_mbuf2' \<sigma> P V j n UNIV \<phi> \<psi> buf \<longleftrightarrow> (case buf of (xs, ys) \<Rightarrow>
  list_all2 (\<lambda>i (r). wf_table n (fv \<phi>) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
    [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) ..< (progress \<sigma> P \<phi> j)] xs \<and>
  list_all2 (\<lambda>i (r). wf_table n (fv \<psi>) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
    [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) ..< (progress \<sigma> P \<psi> j)] ys)"
  unfolding wf_mbuf2'_def wf_mbuf2_def
  by (simp add: mem_restr_UNIV[THEN eqTrueI, abs_def] split: prod.split)

definition wf_ts :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> Formula.formula \<Rightarrow> Formula.formula \<Rightarrow> ts list \<Rightarrow> bool" where
  "wf_ts \<sigma> P j \<phi> \<psi> ts \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j] ts"

definition wf_ts_regex :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> Formula.formula Regex.regex \<Rightarrow> ts list \<Rightarrow> bool" where
  "wf_ts_regex \<sigma> P j r ts \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j] ts"

abbreviation "Sincep pos \<phi> I \<psi> \<equiv> Formula.Since (if pos then \<phi> else Formula.Neg \<phi>) I \<psi>"

definition (in msaux) wf_since_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> event_data list set \<Rightarrow> args \<Rightarrow>
  Formula.formula \<Rightarrow> Formula.formula \<Rightarrow> 'msaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_since_aux \<sigma> V R args \<phi> \<psi> aux ne \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and> (\<exists>cur auxlist. valid_msaux args cur aux auxlist \<and>
    cur = (if ne = 0 then 0 else \<tau> \<sigma> (ne - 1)) \<and>
    sorted_wrt (\<lambda>x y. fst x > fst y) auxlist \<and>
    (\<forall>t X. (t, X) \<in> set auxlist \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne - 1) \<and> memR (args_ivl args) (\<tau> \<sigma> (ne - 1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable (args_n args) (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne-1) (Sincep (args_pos args) \<phi> (point (\<tau> \<sigma> (ne - 1) - t)) \<psi>)) X) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne - 1) \<and> memR (args_ivl args) (\<tau> \<sigma> (ne - 1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set auxlist)))"

definition wf_matchP_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    \<I> \<Rightarrow> Formula.formula Regex.regex \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_matchP_aux \<sigma> V n R I r aux ne \<longleftrightarrow> sorted_wrt (\<lambda>x y. fst x > fst y) aux \<and>
    (\<forall>t X. (t, X) \<in> set aux \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> (ne-1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
      (\<forall>ms \<in> RPDs mr. qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne-1)
         (Formula.MatchP (point (\<tau> \<sigma> (ne-1) - t)) (from_mregex ms \<phi>s)))
         (lookup X ms)))) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> (ne-1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set aux))"

lemma qtable_mem_restr_UNIV: "qtable n A(mem_restr UNIV) Q X = wf_table n A Q X"
  unfolding qtable_def by auto

lemma (in msaux) wf_since_aux_UNIV_alt:
  "wf_since_aux \<sigma> V UNIV args \<phi> \<psi> aux ne \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and> (\<exists>cur auxlist. valid_msaux args cur aux auxlist \<and>
    cur = (if ne = 0 then 0 else \<tau> \<sigma> (ne - 1)) \<and>
    sorted_wrt (\<lambda>x y. fst x > fst y) auxlist \<and>
    (\<forall>t X. (t, X) \<in> set auxlist \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne - 1) \<and> memR (args_ivl args) (\<tau> \<sigma> (ne - 1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      wf_table (args_n args) (Formula.fv \<psi>)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne - 1) (Sincep (args_pos args) \<phi> (point (\<tau> \<sigma> (ne - 1) - t)) \<psi>)) X) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne - 1) \<and> memR (args_ivl args) (\<tau> \<sigma> (ne - 1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set auxlist)))"
  unfolding wf_since_aux_def qtable_mem_restr_UNIV ..

definition wf_until_auxlist :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> bool \<Rightarrow>
    Formula.formula \<Rightarrow> \<I> \<Rightarrow> Formula.formula \<Rightarrow> event_data muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne \<longleftrightarrow>
    list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. if pos then (\<forall>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (map the v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (map the v) k \<phi>)) r1 \<and>
      qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length auxlist \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and>
          Formula.sat \<sigma> V (map the v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (map the v) k \<phi> else \<not> Formula.sat \<sigma> V (map the v) k \<phi>))) r2)
      auxlist [ne..<ne+length auxlist]"

definition (in muaux) wf_until_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> event_data list set \<Rightarrow> args \<Rightarrow>
  Formula.formula \<Rightarrow> Formula.formula \<Rightarrow> 'muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_until_aux \<sigma> V R args \<phi> \<psi> aux ne \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and>
    (\<exists>cur auxlist. valid_muaux args cur aux auxlist \<and>
      cur = (if ne + length auxlist = 0 then 0 else \<tau> \<sigma> (ne + length auxlist - 1)) \<and>
      wf_until_auxlist \<sigma> V (args_n args) R (args_pos args) \<phi> (args_ivl args) \<psi> auxlist ne)"

lemma (in muaux) wf_until_aux_UNIV_alt:
  "wf_until_aux \<sigma> V UNIV args \<phi> \<psi> aux ne \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and>
    (\<exists>cur auxlist. valid_muaux args cur aux auxlist \<and>
      cur = (if ne + length auxlist = 0 then 0 else \<tau> \<sigma> (ne + length auxlist - 1)) \<and>
      list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      wf_table (args_n args) (Formula.fv \<phi>) (\<lambda>v. if (args_pos args)
          then (\<forall>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (map the v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (map the v) k \<phi>)) r1 \<and>
      wf_table (args_n args) (Formula.fv \<psi>) (\<lambda>v. \<exists>j. i \<le> j \<and> j < ne + length auxlist \<and> mem (args_ivl args) (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and>
          Formula.sat \<sigma> V (map the v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if (args_pos args) then Formula.sat \<sigma> V (map the v) k \<phi> else \<not> Formula.sat \<sigma> V (map the v) k \<phi>)) r2)
      auxlist [ne..<ne+length auxlist])"
  unfolding wf_until_aux_def wf_until_auxlist_def qtable_mem_restr_UNIV ..

definition (in mtaux) wf_trigger_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> event_data list set \<Rightarrow> args \<Rightarrow>
  Formula.formula \<Rightarrow> Formula.formula \<Rightarrow> 'mtaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_trigger_aux \<sigma> V R args \<phi> \<psi> aux ne \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and> (\<exists>cur auxlist. valid_mtaux args cur aux (filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist) \<and>
    cur = (if ne = 0 then 0 else \<tau> \<sigma> (ne - 1)) \<and>
    sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist \<and>
    length auxlist = ne \<and>
    (\<forall>(i, (t, l, r)) \<in> set (zip [0..<length auxlist] auxlist). ne \<noteq> 0 \<and> t = \<tau> \<sigma> i \<and> t \<le> \<tau> \<sigma> (ne - 1) \<and>
      qtable (args_n args) (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) l  \<and>
      qtable (args_n args) (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r) \<and>
    (\<forall>i. ne \<noteq> 0 \<and> i \<le> (ne - 1) \<longrightarrow>
      (\<exists>X. (\<tau> \<sigma> i, X) = auxlist!i)))"

definition wf_matchF_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    \<I> \<Rightarrow> Formula.formula Regex.regex \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_matchF_aux \<sigma> V n R I r aux ne k \<longleftrightarrow> (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
      list_all2 (\<lambda>x i. case x of (t, rels, rel) \<Rightarrow> t = \<tau> \<sigma> i \<and>
        list_all2 (\<lambda>\<phi>. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v.
          Formula.sat \<sigma> V (map the v) i \<phi>)) \<phi>s rels \<and>
        qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length aux + k \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and>
          Regex.match (Formula.sat \<sigma> V (map the v)) r i j)) rel)
    aux [ne..<ne+length aux])"

definition wf_matchF_invar where
  "wf_matchF_invar \<sigma> V n R I r st i =
     (case st of (aux, Y) \<Rightarrow> aux \<noteq> [] \<and> wf_matchF_aux \<sigma> V n R I r aux i 0 \<and>
     (case to_mregex r of (mr, \<phi>s) \<Rightarrow> \<forall>ms \<in> LPDs mr.
       qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v.
         Regex.match (Formula.sat \<sigma> V (map the v)) (from_mregex ms \<phi>s) i (i + length aux - 1)) (lookup Y ms)))"

definition lift_envs' :: "nat \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "lift_envs' b R = (\<lambda>(xs,ys). xs @ ys) ` ({xs. length xs = b} \<times> R)"

fun formula_of_constraint :: "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow> Formula.formula" where
  "formula_of_constraint (t1, True, MEq, t2) = Formula.Eq t1 t2"
| "formula_of_constraint (t1, True, MLess, t2) = Formula.Less t1 t2"
| "formula_of_constraint (t1, True, MLessEq, t2) = Formula.LessEq t1 t2"
| "formula_of_constraint (t1, False, MEq, t2) = Formula.Neg (Formula.Eq t1 t2)"
| "formula_of_constraint (t1, False, MLess, t2) = Formula.Neg (Formula.Less t1 t2)"
| "formula_of_constraint (t1, False, MLessEq, t2) = Formula.Neg (Formula.LessEq t1 t2)"

inductive (in maux) wf_mformula :: "Formula.trace \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
  nat \<Rightarrow> event_data list set \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula \<Rightarrow> Formula.formula \<Rightarrow> bool"
  for \<sigma> j where
    Eq: "is_simple_eq t1 t2 \<Longrightarrow>
    \<forall>x\<in>Formula.fv_trm t1. x < n \<Longrightarrow> \<forall>x\<in>Formula.fv_trm t2. x < n \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MRel (eq_rel n t1 t2)) (Formula.Eq t1 t2)"
  | neq_Var: "x < n \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MRel empty_table) (Formula.Neg (Formula.Eq (Formula.Var x) (Formula.Var x)))"
  | Pred: "\<forall>x\<in>Formula.fv (Formula.Pred e ts). x < n \<Longrightarrow>
    \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MPred e ts) (Formula.Pred e ts)"
  | Let: "wf_mformula \<sigma> j P V m UNIV \<phi> \<phi>' \<Longrightarrow>
    wf_mformula \<sigma> j (P(p \<mapsto> progress \<sigma> P \<phi>' j))
      (V(p \<mapsto> \<lambda>i. {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>'})) n R \<psi> \<psi>' \<Longrightarrow>
    {0..<m} \<subseteq> Formula.fv \<phi>' \<Longrightarrow> b \<le> m \<Longrightarrow> m = Formula.nfv \<phi>' \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MLet p m \<phi> \<psi>) (Formula.Let p \<phi>' \<psi>')"
  | And: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>' \<Longrightarrow>
    if pos then \<chi> = Formula.And \<phi>' \<psi>'
      else \<chi> = Formula.And \<phi>' (Formula.Neg \<psi>') \<and> Formula.fv \<psi>' \<subseteq> Formula.fv \<phi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MAnd (fv \<phi>') \<phi> pos (fv \<psi>') \<psi> buf) \<chi>"
  | AndAssign: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow>
    x < n \<Longrightarrow> x \<notin> Formula.fv \<phi>' \<Longrightarrow> Formula.fv_trm t \<subseteq> Formula.fv \<phi>' \<Longrightarrow> (x, t) = conf \<Longrightarrow>
    \<psi>' = Formula.Eq (Formula.Var x) t \<or> \<psi>' = Formula.Eq t (Formula.Var x) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MAndAssign \<phi> conf) (Formula.And \<phi>' \<psi>')"
  | AndRel: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow>
    \<psi>' = formula_of_constraint conf \<Longrightarrow>
    (let (t1, _, _, t2) = conf in Formula.fv_trm t1 \<union> Formula.fv_trm t2 \<subseteq> Formula.fv \<phi>') \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MAndRel \<phi> conf) (Formula.And \<phi>' \<psi>')"
  | And_Trigger: "
    wf_mformula \<sigma> j P V n R \<alpha> \<alpha>' \<Longrightarrow>
    wf_mbuft2' \<sigma> P V j n R \<alpha>' \<phi>'' I \<psi>' buf1 \<Longrightarrow>
    fv (Formula.Trigger \<phi>'' I \<psi>') \<subseteq> fv \<alpha>' \<Longrightarrow>
    wf_mformula \<sigma> j P V n R \<psi> \<psi>' \<Longrightarrow>
    if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>' \<Longrightarrow>
    wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow>
    safe_formula \<phi>'' = args_pos args \<Longrightarrow>
    args_ivl args = I \<Longrightarrow>
    args_n args = n \<Longrightarrow>
    args_L args = Formula.fv \<phi>' \<Longrightarrow>
    args_R args = Formula.fv \<psi>' \<Longrightarrow>
    \<forall>x\<in>Formula.fv \<psi>'. x < n \<Longrightarrow>
    if mem I 0 then
      Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>'
    else
      Formula.fv \<phi>' = Formula.fv \<psi>'
    \<Longrightarrow>
    wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf2 \<Longrightarrow>
    wf_ts \<sigma> P j \<phi>' \<psi>' nts \<Longrightarrow>
    wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Trigger \<phi>'' I \<psi>') j) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MAndTrigger (fv \<alpha>') \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) (Formula.And \<alpha>' (Formula.Trigger \<phi>'' I \<psi>'))"
  | And_Release: "
    \<not>mem I 0 \<Longrightarrow>
    bounded I \<Longrightarrow>
    Formula.fv \<phi>' = Formula.fv \<psi>' \<Longrightarrow>
    wf_mformula \<sigma> j P V n R aux (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') \<Longrightarrow>
    wf_mformula \<sigma> j P V n R aux (Formula.And \<alpha>' (Formula.Release \<phi>' I \<psi>'))"
  | Ands: "list_all2 (\<lambda>\<phi> \<phi>'. wf_mformula \<sigma> j P V n R \<phi> \<phi>') l (l_pos @ map remove_neg l_neg) \<Longrightarrow>
    wf_mbufn (progress \<sigma> P (Formula.Ands l') j) (map (\<lambda>\<psi>. progress \<sigma> P \<psi> j) (l_pos @ map remove_neg l_neg)) (map (\<lambda>\<psi> i.
      qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>)) (l_pos @ map remove_neg l_neg)) buf \<Longrightarrow>
    (l_pos, l_neg) = partition safe_formula l' \<Longrightarrow>
    l_pos \<noteq> [] \<Longrightarrow>
    list_all safe_formula (map remove_neg l_neg) \<Longrightarrow>
    A_pos = map fv l_pos \<Longrightarrow>
    A_neg = map fv l_neg \<Longrightarrow>
    \<Union>(set A_neg) \<subseteq> \<Union>(set A_pos) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MAnds A_pos A_neg l buf) (Formula.Ands l')"
  | Or: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>' \<Longrightarrow>
    Formula.fv \<phi>' = Formula.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MOr \<phi> \<psi> buf) (Formula.Or \<phi>' \<psi>')"
  | Neg: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> Formula.fv \<phi>' = {} \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MNeg \<phi>) (Formula.Neg \<phi>')"
  | Exists: "wf_mformula \<sigma> j P V (Suc n) (lift_envs R) \<phi> \<phi>' \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MExists \<phi>) (Formula.Exists \<phi>')"
  | Agg: "wf_mformula \<sigma> j P V (b + n) (lift_envs' b R) \<phi> \<phi>' \<Longrightarrow>
    y < n \<Longrightarrow>
    y + b \<notin> Formula.fv \<phi>' \<Longrightarrow>
    {0..<b} \<subseteq> Formula.fv \<phi>' \<Longrightarrow>
    Formula.fv_trm f \<subseteq> Formula.fv \<phi>' \<Longrightarrow>
    g0 = (Formula.fv \<phi>' \<subseteq> {0..<b}) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MAgg g0 y \<omega> b f \<phi>) (Formula.Agg y \<omega> b f \<phi>')"
  | Prev: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow>
    first \<longleftrightarrow> j = 0 \<Longrightarrow>
    list_all2 (\<lambda>i (r). qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>') r)
      [min (progress \<sigma> P \<phi>' j) (j-1)..<progress \<sigma> P \<phi>' j] buf \<Longrightarrow>
    list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi>' j) (j-1)..<j] nts \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MPrev I \<phi> first buf nts) (Formula.Prev I \<phi>')"
  | Next: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow>
    first \<longleftrightarrow> progress \<sigma> P \<phi>' j = 0 \<Longrightarrow>
    list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress \<sigma> P \<phi>' j - 1..<j] nts \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MNext I \<phi> first nts) (Formula.Next I \<phi>')"
  | Since: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>' \<Longrightarrow>
    if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>' \<Longrightarrow>
    safe_formula \<phi>'' = args_pos args \<Longrightarrow>
    args_ivl args = I \<Longrightarrow>
    args_n args = n \<Longrightarrow>
    args_L args = Formula.fv \<phi>' \<Longrightarrow>
    args_R args = Formula.fv \<psi>' \<Longrightarrow>
    Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_ts \<sigma> P j \<phi>' \<psi>' nts \<Longrightarrow>
    wf_since_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Since \<phi>'' I \<psi>') j) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MSince args \<phi> \<psi> buf nts aux) (Formula.Since \<phi>'' I \<psi>')"
  | Until: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>' \<Longrightarrow>
    if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>' \<Longrightarrow>
    safe_formula \<phi>'' = args_pos args \<Longrightarrow>
    args_ivl args = I \<Longrightarrow>
    args_n args = n \<Longrightarrow>
    args_L args = Formula.fv \<phi>' \<Longrightarrow>
    args_R args = Formula.fv \<psi>' \<Longrightarrow>
    Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_ts \<sigma> P j \<phi>' \<psi>' nts \<Longrightarrow>
    t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j)))) \<Longrightarrow>
    wf_until_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Until \<phi>'' I \<psi>') j) \<Longrightarrow>
    progress \<sigma> P (Formula.Until \<phi>'' I \<psi>') j + length_muaux args aux = min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MUntil args \<phi> \<psi> buf nts t aux) (Formula.Until \<phi>'' I \<psi>')"
  | Trigger_0: "
    wf_mformula \<sigma> j P V n R \<psi> \<psi>' \<Longrightarrow>
    if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>' \<Longrightarrow>
    wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow>
    safe_formula \<phi>'' = args_pos args \<Longrightarrow>
    args_ivl args = I \<Longrightarrow>
    args_n args = n \<Longrightarrow>
    args_L args = Formula.fv \<phi>' \<Longrightarrow>
    args_R args = Formula.fv \<psi>' \<Longrightarrow>
    \<forall>x\<in>Formula.fv \<psi>'. x < n \<Longrightarrow>
    if mem I 0 then (Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>') else Formula.fv \<phi>' = Formula.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_ts \<sigma> P j \<phi>' \<psi>' nts \<Longrightarrow>
    wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Trigger \<phi>'' I \<psi>') j) \<Longrightarrow>
    mem I 0 \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MTrigger args \<phi> \<psi> buf nts aux) (Formula.Trigger \<phi>'' I \<psi>')"
  | Release_0: "
    mem I 0 \<Longrightarrow>
    bounded I \<Longrightarrow>
    Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow>
    wf_mformula \<sigma> j P V n R aux (release_safe_0 \<phi>' I \<psi>') \<Longrightarrow>
    wf_mformula \<sigma> j P V n R aux (Formula.Release \<phi>' I \<psi>')"
  | MatchP: "(case to_mregex r of (mr', \<phi>s') \<Rightarrow>
      list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<phi>s' \<and> mr = mr') \<Longrightarrow>
    mrs = sorted_list_of_set (RPDs mr) \<Longrightarrow>
    safe_regex Past Strict r \<Longrightarrow>
    wf_mbufn' \<sigma> P V j n R r buf \<Longrightarrow>
    wf_ts_regex \<sigma> P j r nts \<Longrightarrow>
    wf_matchP_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchP I r) j) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MMatchP I mr mrs \<phi>s buf nts aux) (Formula.MatchP I r)"
  | MatchF: "(case to_mregex r of (mr', \<phi>s') \<Rightarrow>
      list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<phi>s' \<and> mr = mr') \<Longrightarrow>
    mrs = sorted_list_of_set (LPDs mr) \<Longrightarrow>
    safe_regex Futu Strict r \<Longrightarrow>
    wf_mbufn' \<sigma> P V j n R r buf \<Longrightarrow>
    wf_ts_regex \<sigma> P j r nts \<Longrightarrow>
    t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (progress_regex \<sigma> P r j))) \<Longrightarrow>
    wf_matchF_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchF I r) j) 0 \<Longrightarrow>
    progress \<sigma> P (Formula.MatchF I r) j + length aux = progress_regex \<sigma> P r j \<Longrightarrow>
    wf_mformula \<sigma> j P V n R (MMatchF I mr mrs \<phi>s buf nts t aux) (Formula.MatchF I r)"

definition (in maux) wf_mstate :: "Formula.formula \<Rightarrow> Formula.prefix \<Rightarrow> event_data list set \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate \<Rightarrow> bool" where
  "wf_mstate \<phi> \<pi> R st \<longleftrightarrow> mstate_n st = Formula.nfv \<phi> \<and> (\<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow>
    mstate_i st = progress \<sigma> Map.empty \<phi> (plen \<pi>) \<and>
    wf_mformula \<sigma> (plen \<pi>) Map.empty Map.empty (mstate_n st) R (mstate_m st) \<phi>)"


subsubsection \<open>Initialisation\<close>

lemma wf_mbuf2'_0: "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> wf_mbuf2' \<sigma> P V 0 n R \<phi> \<psi> ([], [])"
  unfolding wf_mbuf2'_def wf_mbuf2_def by simp

lemma wf_mbufn'_0: "to_mregex r = (mr, \<phi>s) \<Longrightarrow> pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> wf_mbufn' \<sigma> P V 0 n R r (replicate (length \<phi>s) [])"
  unfolding wf_mbufn'_def wf_mbufn_def map_replicate_const[symmetric]
  by (auto simp: list_all3_map intro: list_all3_refl simp: Min_eq_iff progress_regex_def)

lemma wf_ts_0: "wf_ts \<sigma> P 0 \<phi> \<psi> []"
  unfolding wf_ts_def by simp

lemma wf_ts_regex_0: "wf_ts_regex \<sigma> P 0 r []"
  unfolding wf_ts_regex_def by simp

lemma (in msaux) wf_since_aux_Nil: "Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow>
  wf_since_aux \<sigma> V R (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') b) \<phi>' \<psi>' (init_msaux (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') b)) 0"
  unfolding wf_since_aux_def by (auto intro!: valid_init_msaux)

lemma (in muaux) wf_until_aux_Nil: "Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow>
  wf_until_aux \<sigma> V R (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') b) \<phi>' \<psi>' (init_muaux (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') b)) 0"
  unfolding wf_until_aux_def wf_until_auxlist_def by (auto intro: valid_init_muaux)

lemma wf_matchP_aux_Nil: "wf_matchP_aux \<sigma> V n R I r [] 0"
  unfolding wf_matchP_aux_def by simp

lemma wf_matchF_aux_Nil: "wf_matchF_aux \<sigma> V n R I r [] 0 k"
  unfolding wf_matchF_aux_def by simp

lemma fv_regex_alt: "safe_regex m g r \<Longrightarrow> Formula.fv_regex r = (\<Union>\<phi> \<in> atms r. Formula.fv \<phi>)"
  unfolding fv_regex_alt atms_def
  by (auto 0 3 dest: safe_regex_safe_formula)

lemmas to_mregex_atms =
  to_mregex_ok[THEN conjunct1, THEN equalityD1, THEN set_mp, rotated]

lemma (in maux) wf_minit0: "safe_formula \<phi> \<Longrightarrow> \<forall>x\<in>Formula.fv \<phi>. x < n \<Longrightarrow>
  pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow>
  wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
proof (induction arbitrary: n R P V rule: safe_formula_induct)
  case (Eq_Const c d)
  then have wf_props:
    "is_simple_eq (trm.Const c) (trm.Const d)"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    "\<forall>x\<in>fv_trm (trm.Const d). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (Eq_Var1 c x)
  then have wf_props:
    "is_simple_eq (trm.Const c) (trm.Var x)"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    "\<forall>x\<in>fv_trm (trm.Var x). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (Eq_Var2 c x)
  then have wf_props:
    "is_simple_eq (trm.Var x) (trm.Const c)"
    "\<forall>x\<in>fv_trm (trm.Var x). x < n"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (neq_Var x n)
  then show ?case by (auto intro!: wf_mformula.neq_Var)
next
  case (Pred e ts)
  then show ?case by (auto intro!: wf_mformula.Pred)
next
  case (Let p \<phi> \<psi>)
  with fvi_less_nfv show ?case
    by (auto simp: pred_mapping_alt dom_def intro!: wf_mformula.Let Let(4,5))
next
  case (And_assign \<phi> \<psi>)
  then have 1: "\<forall>x\<in>fv \<psi>. x < n" by simp
  from 1 \<open>safe_assignment (fv \<phi>) \<psi>\<close>
  obtain x t where
    "x < n" "x \<notin> fv \<phi>" "fv_trm t \<subseteq> fv \<phi>"
    "\<psi> = Formula.Eq (Formula.Var x) t \<or> \<psi> = Formula.Eq t (Formula.Var x)"
    unfolding safe_assignment_def by (force split: formula.splits trm.splits)
  with And_assign show ?case
    by (auto intro!: wf_mformula.AndAssign split: trm.splits)
next
  case (And_safe \<phi> \<psi>)
  then show ?case by (auto intro!: wf_mformula.And wf_mbuf2'_0)
next
  case (And_constraint \<phi> \<psi>)
  from \<open>fv \<psi> \<subseteq> fv \<phi>\<close> \<open>is_constraint \<psi>\<close>
  obtain t1 p c t2 where
    "(t1, p, c, t2) = split_constraint \<psi>"
    "formula_of_constraint (split_constraint \<psi>) = \<psi>"
    "fv_trm t1 \<union> fv_trm t2 \<subseteq> fv \<phi>"
    by (induction rule: is_constraint.induct) auto
  with And_constraint show ?case
    by (auto 0 3 intro!: wf_mformula.AndRel)
next
  case (And_Not \<phi> \<psi>)
  then show ?case by (auto intro!: wf_mformula.And wf_mbuf2'_0)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
    using And_Trigger(5,8,9)
    by auto
  define t where "t = formula.Trigger \<phi>' I \<psi>'"
  define f where "f = formula.And \<phi> t"
  define args where "args = (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') True)"
  define aux where "aux = (init_mtaux args)"

 have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
  unfolding safe_assignment_def
  by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have wf_\<phi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
    using And_Trigger(6,8,9)
    by auto
  have wf_\<psi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>') \<psi>'"
    using And_Trigger(7,8,9)
    by auto
  have if_pos: "if args_pos args then \<phi>' = \<phi>' else \<phi>' = formula.Neg \<phi>'"
    unfolding args_def init_args_def
    by auto
  have args: "safe_formula \<phi>' = args_pos args"
    "args_ivl args = I"
    "args_n args = n"
    "args_L args = fv \<phi>'"
    "args_R args = fv \<psi>'"
    "\<forall>x\<in>fv \<psi>'. x < n"
    "if mem I 0 then fv \<phi>' \<subseteq> fv \<psi>' else fv \<phi>' = fv \<psi>'"
    using And_Trigger(2,3,8)
    unfolding args_def init_args_def safe_formula_dual_def
    by auto

  have buf_ts:
    "wf_mbuf2' \<sigma> P V 0 n R \<phi>' \<psi>' ([], [])"
    "wf_ts \<sigma> P 0 \<phi>' \<psi>' []"
    unfolding wf_mbuf2'_def wf_mbuf2_def wf_ts_def
    by (auto simp add: And_Trigger(9))

  have aux: "wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (Monitor.progress \<sigma> P (formula.Trigger \<phi>' I \<psi>') 0)"
    using And_Trigger(3) valid_init_mtaux[of I "fv \<phi>'" "fv \<psi>'" True n]
    unfolding safe_formula_dual_def wf_trigger_aux_def aux_def args_def
    by (auto simp add: Let_def And_Trigger(9) split: if_splits)

  have if_pos: "if args_pos args then \<phi>' = \<phi>' else \<phi>' = formula.Neg \<phi>'"
    unfolding args_def init_args_def
    by auto
  have wf_buf:
    "wf_mbuf2' \<sigma> P V 0 n R \<phi> t ([], [])"
    "wf_mbuft2' \<sigma> P V 0 n R \<phi> \<phi>' I \<psi>' ([], [])"
    "wf_mbuf2' \<sigma> P V 0 n R \<phi>' \<psi>' ([],[])"
    "wf_ts \<sigma> P 0  \<phi>' \<psi>' []"
    unfolding wf_mbuf2'_def wf_mbuft2'_def wf_mbuf2_def wf_mbuf2_def wf_ts_def
    by (auto simp add: And_Trigger(9))

  show ?case
  proof (cases "safe_formula t")
    case True
    then have mem: "mem I 0"
      unfolding t_def
      by (auto simp add: safe_formula_dual_def split: if_splits)

    have wf_t: "wf_mformula \<sigma> 0 P V n R (minit0 n t) t"
      using And_Trigger(2) wf_mformula.Trigger_0[OF wf_\<psi>' if_pos wf_\<phi>' args buf_ts aux mem]
      unfolding t_def aux_def args_def
      by (auto split: if_splits)
    show ?thesis using wf_mformula.And[OF wf_\<phi> wf_t _ wf_buf(1)]
      using True And_Trigger(2) t_not_safe_assign t_not_constraint
      unfolding f_def t_def args_def aux_def
      by (auto split: if_splits)
  next
    case False
    then show ?thesis using wf_mformula.And_Trigger[OF wf_\<phi> wf_buf(2)[unfolded t_def] And_Trigger(4) wf_\<psi>' if_pos wf_\<phi>' args wf_buf(3-4) aux]
      using And_Trigger(2) t_not_safe_assign t_not_constraint
      unfolding f_def t_def args_def aux_def
      by (auto split: if_splits)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  note fvs = release_fvi(3)[of 0 \<phi> \<phi>' I \<psi>']
  have fv_eq: "fv (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) = fv \<phi>"
    using And_Release(7)
    by auto
  then have release_subformulas:
    "\<forall>x\<in>fv \<phi>'. x < n"
    "\<forall>x\<in>fv \<psi>'. x < n"
    using And_Release(7) And_Release.prems(1)
    unfolding fvi.simps
    by auto
  have wf_formula:
    "wf_mformula \<sigma> 0 P V n R (minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')) (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>') \<psi>'"
    using And_Release.IH(1)[OF And_Release.prems(1)[unfolded fvs]]
          And_Release.IH(2)[OF And_Release.prems(1)[unfolded fv_eq]]
          And_Release.IH(3)[OF release_subformulas(1)]
          And_Release.IH(4)[OF release_subformulas(2)]
      And_Release.prems(2)
    by auto
  have "\<not> safe_assignment (fv \<phi>) (formula.Release \<phi>' I \<psi>')"
    unfolding safe_assignment_def
    by auto
  moreover have "\<not> safe_formula (formula.Release \<phi>' I \<psi>')"
    using And_Release(6)
    by auto
  moreover have "\<not> is_constraint (formula.Release \<phi>' I \<psi>')"
    by auto
  ultimately have "minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>') = minit0 n (formula.And \<phi> (formula.Release \<phi>' I \<psi>'))"
    by auto
  then show ?case using wf_mformula.And_Release[OF And_Release(6,5,4) wf_formula(1)]
    by auto
next
  case (Ands l pos neg)
  define mpos where "mpos = map (minit0 n) (pos)"
  define mneg where "mneg = map (minit0 n) (map remove_neg neg)"

  have fvs_l: "\<forall>\<phi> \<in> (set pos \<union> set neg). \<forall>x\<in>fv \<phi>. x < n"
    using Ands(1,8)
    by auto
  moreover have "list_all (\<lambda>\<phi>. (\<forall>x\<in>fv \<phi>. x < n) \<longrightarrow> pred_mapping (\<lambda>x. x = 0) P \<longrightarrow> wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>) pos"
    using Ands(6)
    unfolding list_all_iff
    by auto
  ultimately have "list_all (\<lambda>\<phi>. wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>) pos"
    using Ands(9)
    unfolding list_all_iff
    by blast
  then have "list_all2 (wf_mformula \<sigma> 0 P V n R) (map (minit0 n) pos) pos"
    by (induction pos) (auto)
  then have pos: "list_all2 (wf_mformula \<sigma> 0 P V n R) mpos pos"
    unfolding mpos_def list_all2_iff
    by auto

  {
    fix \<phi>
    assume "\<phi>\<in>set (map remove_neg neg)"
    then obtain \<phi>' where \<phi>'_props: "\<phi> = remove_neg \<phi>'" "\<phi>' \<in> set neg"
      by auto
    moreover have "\<not> safe_formula \<phi>'"
      using Ands(1) \<phi>'_props(2)
      by auto
    ultimately have \<phi>'_eq:
      "\<phi>' = Formula.Neg \<phi>"
      using ballE[OF Ands(4)[unfolded list_all_iff], of \<phi>' False]
      by (cases \<phi>') (auto)
    then have "(\<forall>x\<in>fv \<phi>. x < n) \<longrightarrow> pred_mapping (\<lambda>x. x = 0) P \<longrightarrow> wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
      using Ands(7) \<phi>'_props(2)
      unfolding list_all_iff
      by auto
    moreover have "(\<forall>x\<in>fv \<phi>. x < n)"
      using fvs_l \<phi>'_props fv_remove_neg
      by auto
    moreover have "safe_formula \<phi>"
      using ballE[OF Ands(4)[unfolded list_all_iff], of \<phi>' False] \<phi>'_props
      unfolding list_all_iff
      by (cases \<phi>') (auto)
    ultimately have
      "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
      "safe_formula \<phi>"
      using Ands(1,9)
      by auto
  }
  then have list_all_remove_neg:
    "list_all (\<lambda>\<phi>. wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>) (map remove_neg neg)"
    "list_all (\<lambda>\<phi>. safe_formula \<phi>) (map remove_neg neg)"
    unfolding list_all_def
    by auto
  then have neg: "list_all2 (wf_mformula \<sigma> 0 P V n R) mneg (map remove_neg neg)"
    unfolding mneg_def
    by (induction neg) (auto)
  then have wf_l: "list_all2 (wf_mformula \<sigma> 0 P V n R) (mpos @ mneg) (pos @ map remove_neg neg)"
    using pos
    unfolding list_all2_iff
    by auto

  have len: "length pos + length neg = length l"
    using Ands(1) sum_length_filter_compl
    by (auto simp add: o_def)

  have qtable: "wf_mbufn (Monitor.progress \<sigma> P (formula.Ands l) 0) (map (\<lambda>\<psi>. Monitor.progress \<sigma> P \<psi> 0) (pos @ map remove_neg neg))
   (map (\<lambda>\<psi> i (r). qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r) (pos @ map remove_neg neg)) (replicate (length l) [])"
    using len Ands(1,2) Ands.prems(2)
    apply (auto
        simp add: wf_mbufn_def list_all3_map list.rel_map map_replicate_const[symmetric]
        simp del: map_append
    )
    apply (auto simp add: list_all3_list_all2_eq list_all2_iff)
    by (metis f_arg_min_list_f)

  define A_pos where "A_pos = map fv pos"
  define A_neg where "A_neg = map fv neg"

  have fvs: "\<Union> (set A_neg) \<subseteq> \<Union> (set A_pos)"
    using Ands(5)
    unfolding A_pos_def A_neg_def
    by auto

  have "wf_mformula \<sigma> 0 P V n R (MAnds A_pos A_neg (mpos @ mneg) (replicate (length l) [])) (formula.Ands l)"
    using wf_mformula.Ands[OF wf_l qtable Ands(1-2) list_all_remove_neg(2) A_pos_def A_neg_def fvs]
    by auto

  then show ?case
    using Ands(1)
    unfolding mpos_def mneg_def A_pos_def A_neg_def
    by auto
next
  case (Neg \<phi>)
  then show ?case by (auto intro!: wf_mformula.Neg)
next
  case (Or \<phi> \<psi>)
  then show ?case by (auto intro!: wf_mformula.Or wf_mbuf2'_0)
next
  case (Exists \<phi>)
  then show ?case by (auto simp: fvi_Suc_bound intro!: wf_mformula.Exists[unfolded fvi.simps])
next
  case (Agg y \<omega> b f \<phi>)
  have "\<forall>x\<in>fv \<phi>. x < b + n"
    using Agg
    by (auto intro!: fvi_plus_bound)
  then have "wf_mformula \<sigma> 0 P V (b + n) (lift_envs' b R) (minit0 (b + n) \<phi>) \<phi>"
    using Agg(7) Agg.IH[of "b + n" P V "(lift_envs' b R)"]
    by auto
  then show ?case
    using Agg wf_mformula.Agg[unfolded fvi.simps, of \<sigma> 0 P V b n R "(minit0 (b + n) \<phi>)" \<phi> y f "(fv \<phi> \<subseteq> {0..<b})" \<omega>]
    by (auto)
next
  case (Prev I \<phi>)
  thm wf_mformula.Prev[where P=P]
  then show ?case by (auto intro!: wf_mformula.Prev)
next
  case (Next I \<phi>)
  then show ?case by (auto intro!: wf_mformula.Next)
next
  case (Since \<phi> I \<psi>)
  then show ?case
    using wf_since_aux_Nil
    by (auto simp add: init_args_def intro!: wf_mformula.Since wf_mbuf2'_0 wf_ts_0)
next
  case (Not_Since \<phi> I \<psi>)
  then show ?case
    using wf_since_aux_Nil
    by (auto simp add: init_args_def intro!: wf_mformula.Since wf_mbuf2'_0 wf_ts_0)
next
  case (Until \<phi> I \<psi>)
  then show ?case
    using valid_length_muaux[OF valid_init_muaux[OF Until(1)]] wf_until_aux_Nil
    by (auto simp add: init_args_def simp del: progress_simps intro!: wf_mformula.Until[unfolded fvi.simps] wf_mbuf2'_0 wf_ts_0)
next
  case (Not_Until \<phi> I \<psi>)
  define args where "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False"

  have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
    using Not_Until(5)[of n P V R] Not_Until(7,8)
    by auto
  have wf_\<psi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>) \<psi>"
    using Not_Until(6)[of n P V R] Not_Until(7,8)
    by auto
  have args:
    "if args_pos args then formula.Neg \<phi> = \<phi> else formula.Neg \<phi> = formula.Neg \<phi>"
    "safe_formula (formula.Neg \<phi>) = args_pos args"
    "args_ivl args = I"
    "args_n args = n"
    "args_L args = fv \<phi>"
    "args_R args = fv \<psi>"
    "fv \<phi> \<subseteq> fv \<psi>"
    using Not_Until(1,3)
    unfolding args_def init_args_def
    by auto

  have wf_aux: "wf_until_aux \<sigma> V R args \<phi> \<psi> (init_muaux args) (Monitor.progress \<sigma> P (formula.Until (formula.Neg \<phi>) I \<psi>) 0)"
    using wf_until_aux_Nil[OF args(7)] Not_Until(8)
    unfolding args_def 
    by (auto simp del: progress_simps)

  have muax_len: "length_muaux args (init_muaux args) = length []"
    using valid_length_muaux[OF valid_init_muaux[OF Not_Until(1)], of I n False]
    unfolding args_def
    by auto
  then have prog:
    "0 = (if 0 = 0 then 0 else \<tau> \<sigma> (min (0 - 1) (min (Monitor.progress \<sigma> P \<phi> 0) (Monitor.progress \<sigma> P \<psi> 0))))"
    "Monitor.progress \<sigma> P (formula.Until (formula.Neg \<phi>) I \<psi>) 0 + length_muaux args (init_muaux args) = min (Monitor.progress \<sigma> P \<phi> 0) (Monitor.progress \<sigma> P \<psi> 0)"
    using Inf_UNIV_nat Not_Until(8)
    by auto
  
  show ?case
    using wf_mformula.Until[unfolded fvi.simps, OF wf_\<phi> wf_\<psi> args wf_mbuf2'_0[OF Not_Until(8)] wf_ts_0 prog(1) wf_aux prog(2)] Not_Until(3)
    unfolding args_def
    by auto
    
next
  case (Trigger_0 \<phi> I \<psi>)
  have wf_\<psi>:
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>) \<psi>"
    using Trigger_0
    by auto
  show ?case
  proof (cases "safe_formula \<phi> \<and> (\<forall>x. (\<forall>xa\<in>fv \<phi>. xa < x) \<longrightarrow> (\<forall>xa xaa. pred_mapping (\<lambda>x. x = 0) xaa \<longrightarrow> (\<forall>xaaa. wf_mformula \<sigma> 0 xaa xaaa x xa (minit0 x \<phi>) \<phi>)))")
    define args where "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True"
    define aux where "aux = init_mtaux args"
    case True
    then have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
      using Trigger_0
      by auto
    have if_pos: "if args_pos args then \<phi> = \<phi> else \<phi> = formula.Neg \<phi>"
      unfolding args_def init_args_def
      by auto
    have args:
      "safe_formula \<phi> = args_pos args"
      "args_ivl args = I"
      "args_n args = n"
      "args_L args = fv \<phi>"
      "args_R args = fv \<psi>"
      "\<forall>x\<in>fv \<psi>. x < n"
      "if mem I 0 then fv \<phi> \<subseteq> fv \<psi> else fv \<phi> = fv \<psi>"
      and mem: "mem I 0"
      using Trigger_0(1,3,6) True
      unfolding args_def init_args_def
      by auto
    have aux: "wf_trigger_aux \<sigma> V R args \<phi> \<psi> aux (Monitor.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
      using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>" "fv \<psi>" True n]
      unfolding safe_formula_dual_def wf_trigger_aux_def aux_def args_def
      by (auto simp add: Let_def Trigger_0(7) split: if_splits)

    show ?thesis
      using True wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi> args wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux mem]
      unfolding aux_def args_def
      by auto
  next
    define args where "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True"
    define aux where "aux = init_mtaux args"
    case False
    then obtain \<phi>' where \<phi>'_props:
      "\<phi> = Formula.Neg \<phi>'"
      "safe_formula \<phi>'"
      "(\<forall>x. (\<forall>xa\<in>fv \<phi>'. xa < x) \<longrightarrow> (\<forall>xa xaa. pred_mapping (\<lambda>x. x = 0) xaa \<longrightarrow> (\<forall>xaaa. wf_mformula \<sigma> 0 xaa xaaa x xa (minit0 x \<phi>') \<phi>')))"
      using Trigger_0(4)
      by (cases \<phi>) (auto)
    show ?thesis
    proof (cases "safe_formula \<phi>")
      case True
      then have "fv \<phi>' = {}"
        using \<phi>'_props(1,2) safe_formula_Neg[of \<phi>']
        by auto
      moreover have "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
        using Trigger_0(6,7) \<phi>'_props(1,3)
        by auto
      ultimately have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
        using \<phi>'_props(1) wf_mformula.Neg
        by auto
      have if_pos: "if args_pos args then \<phi> = \<phi> else \<phi> = formula.Neg \<phi>"
        unfolding args_def init_args_def
        by auto
      have args:
        "safe_formula \<phi> = args_pos args"
        "args_ivl args = I"
        "args_n args = n"
        "args_L args = fv \<phi>"
        "args_R args = fv \<psi>"
        "\<forall>x\<in>fv \<psi>. x < n"
        "if mem I 0 then fv \<phi> \<subseteq> fv \<psi> else fv \<phi> = fv \<psi>"
        and mem: "mem I 0"
        using Trigger_0(1,3,6) True
        unfolding args_def init_args_def
        by auto
      have aux: "wf_trigger_aux \<sigma> V R args \<phi> \<psi> aux (Monitor.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
        using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>" "fv \<psi>" True n]
        unfolding safe_formula_dual_def wf_trigger_aux_def aux_def args_def
        by (auto simp add: Let_def Trigger_0(7) split: if_splits)
  
      show ?thesis
        using True wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi> args wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux mem]
        unfolding aux_def args_def
        by auto
    next
      define args where "args = init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>) False"
      define aux where "aux = init_mtaux args"
      case False
      have wf_\<phi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
        using \<phi>'_props Trigger_0
        by auto
      have if_pos: "if args_pos args then \<phi> = \<phi>' else \<phi> = formula.Neg \<phi>'"
        unfolding \<phi>'_props(1) args_def init_args_def
        by auto
      have args:
        "safe_formula \<phi> = args_pos args"
        "args_ivl args = I"
        "args_n args = n"
        "args_L args = fv \<phi>'"
        "args_R args = fv \<psi>"
        "\<forall>x\<in>fv \<psi>. x < n"
        "if mem I 0 then fv \<phi>' \<subseteq> fv \<psi> else fv \<phi>' = fv \<psi>"
        and mem: "mem I 0"
        using \<phi>'_props(1) Trigger_0(1,3,6) False
        unfolding args_def init_args_def
        by auto
      have aux: "wf_trigger_aux \<sigma> V R args \<phi>' \<psi> aux (Monitor.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
        using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>'" "fv \<psi>" False n] \<phi>'_props(1)
        unfolding safe_formula_dual_def wf_trigger_aux_def aux_def args_def
        by (auto simp add: Let_def Trigger_0(7) split: if_splits)
  
      show ?thesis
        using False \<phi>'_props(1) wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi>' args wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux mem]
        unfolding aux_def args_def
        by auto
    qed
  qed
next
  case (Trigger \<phi> I \<psi>)
  then show ?case by auto
next
  case (Release_0 \<phi> I \<psi>)
  have "wf_mformula \<sigma> 0 P V n R (minit0 n (release_safe_0 \<phi> I \<psi>)) (release_safe_0 \<phi> I \<psi>)"
    using Release_0.IH[OF Release_0.prems[unfolded release_fvi(1)]]
    by auto
  then show ?case
    using minit0_release_0[OF Release_0(1)] wf_mformula.Release_0[OF Release_0(1-2,4)]
    by (auto)
next
  case (Release \<phi> I \<psi>)
  then show ?case by auto
next
  case (MatchP I r)
  obtain mr \<phi>s' where r_props:"(mr, \<phi>s') = to_mregex r"
    by (metis surj_pair)
  define \<phi>s where "\<phi>s = (map (minit0 n) \<phi>s')"

  have wf_props:
    "case to_mregex r of (mr', \<phi>s') \<Rightarrow> list_all2 (wf_mformula \<sigma> 0 P V n R) \<phi>s \<phi>s' \<and> mr = mr'"
    "(sorted_list_of_set (RPDs mr)) = sorted_list_of_set (RPDs mr)"
    "safe_regex Past Strict r"
    "wf_mbufn' \<sigma> P V 0 n R r (replicate (length \<phi>s') [])"
    "wf_ts_regex \<sigma> P 0 r []"
    "wf_matchP_aux \<sigma> V n R I r [] (Monitor.progress \<sigma> P (formula.MatchP I r) 0)"
    using MatchP r_props
    unfolding \<phi>s_def
    by (auto simp: list.rel_map fv_regex_alt simp del: progress_simps split: prod.split
        intro!: list.rel_refl_strong wf_mbufn'_0[OF r_props[symmetric]] wf_ts_regex_0 wf_matchP_aux_Nil
        dest!: to_mregex_atms)
  show ?case
    using wf_mformula.MatchP[OF wf_props] r_props
    unfolding \<phi>s_def
    by (cases "to_mregex r") (auto)
next
  case (MatchF I r)
  obtain mr \<phi>s' where r_props:"(mr, \<phi>s') = to_mregex r"
    by (metis surj_pair)
  define \<phi>s where "\<phi>s = (map (minit0 n) \<phi>s')"

  have wf_props:
    "case to_mregex r of (mr', \<phi>s') \<Rightarrow> list_all2 (wf_mformula \<sigma> 0 P V n R) \<phi>s \<phi>s' \<and> mr = mr'"
    "sorted_list_of_set (LPDs mr) = sorted_list_of_set (LPDs mr)"
    "safe_regex Futu Strict r"
    "wf_mbufn' \<sigma> P V 0 n R r (replicate (length \<phi>s') [])"
    "wf_ts_regex \<sigma> P 0 r []"
    "0 = (if 0 = 0 then 0 else \<tau> \<sigma> (min (0 - 1) (progress_regex \<sigma> P r 0)))"
    "wf_matchF_aux \<sigma> V n R I r [] (Monitor.progress \<sigma> P (formula.MatchF I r) 0) 0"
    "Monitor.progress \<sigma> P (formula.MatchF I r) 0 + length [] = progress_regex \<sigma> P r 0"
    using MatchF r_props
    unfolding \<phi>s_def
    by (auto simp: list.rel_map fv_regex_alt progress_le Min_eq_iff progress_regex_def
        simp del: progress_simps split: prod.split
        intro!: list.rel_refl_strong wf_mbufn'_0[OF r_props[symmetric]] wf_ts_regex_0 wf_matchF_aux_Nil
        dest!: to_mregex_atms)
  show ?case
    using wf_mformula.MatchF[OF wf_props] r_props
    unfolding \<phi>s_def
    by (cases "to_mregex r") (auto)
qed

lemma (in maux) wf_mstate_minit: "safe_formula \<phi> \<Longrightarrow> wf_mstate \<phi> pnil R (minit \<phi>)"
  unfolding wf_mstate_def minit_def Let_def
  by (auto intro!: wf_minit0 fvi_less_nfv)

subsubsection \<open>Evaluation\<close>

lemma match_wf_tuple: "Some f = match ts xs \<Longrightarrow>
  wf_tuple n (\<Union>t\<in>set ts. Formula.fv_trm t) (Table.tabulate f 0 n)"
  by (induction ts xs arbitrary: f rule: match.induct)
    (fastforce simp: wf_tuple_def split: if_splits option.splits)+

lemma match_fvi_trm_None: "Some f = match ts xs \<Longrightarrow> \<forall>t\<in>set ts. x \<notin> Formula.fv_trm t \<Longrightarrow> f x = None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_fvi_trm_Some: "Some f = match ts xs \<Longrightarrow> t \<in> set ts \<Longrightarrow> x \<in> Formula.fv_trm t \<Longrightarrow> f x \<noteq> None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_eval_trm: "\<forall>t\<in>set ts. \<forall>i\<in>Formula.fv_trm t. i < n \<Longrightarrow> Some f = match ts xs \<Longrightarrow>
    map (Formula.eval_trm (Table.tabulate (\<lambda>i. the (f i)) 0 n)) ts = xs"
proof (induction ts xs arbitrary: f rule: match.induct)
  case (3 x ts y ys)
  from 3(1)[symmetric] 3(2,3) show ?case
    by (auto 0 3 dest: match_fvi_trm_Some sym split: option.splits if_splits intro!: eval_trm_fv_cong)
qed (auto split: if_splits)

lemma wf_tuple_tabulate_Some: "wf_tuple n A (Table.tabulate f 0 n) \<Longrightarrow> x \<in> A \<Longrightarrow> x < n \<Longrightarrow> \<exists>y. f x = Some y"
  unfolding wf_tuple_def by auto

lemma ex_match: "wf_tuple n (\<Union>t\<in>set ts. Formula.fv_trm t) v \<Longrightarrow>
  \<forall>t\<in>set ts. (\<forall>x\<in>Formula.fv_trm t. x < n) \<and> (Formula.is_Var t \<or> Formula.is_Const t) \<Longrightarrow>
  \<exists>f. match ts (map (Formula.eval_trm (map the v)) ts) = Some f \<and> v = Table.tabulate f 0 n"
proof (induction ts "map (Formula.eval_trm (map the v)) ts" arbitrary: v rule: match.induct)
  case (3 x ts y ys)
  then show ?case
  proof (cases "x \<in> (\<Union>t\<in>set ts. Formula.fv_trm t)")
    case True
    with 3 show ?thesis
      by (auto simp: insert_absorb dest!: wf_tuple_tabulate_Some meta_spec[of _ v])
  next
    case False
    with 3(3,4) have
      *: "map (Formula.eval_trm (map the v)) ts = map (Formula.eval_trm (map the (v[x := None]))) ts"
      by (auto simp: wf_tuple_def nth_list_update intro!: eval_trm_fv_cong)
    from False 3(2-4) obtain f where
      "match ts (map (Formula.eval_trm (map the v)) ts) = Some f" "v[x := None] = Table.tabulate f 0 n"
      unfolding *
      by (atomize_elim, intro 3(1)[of "v[x := None]"])
        (auto simp: wf_tuple_def nth_list_update intro!: eval_trm_fv_cong)
    moreover from False this have "f x = None" "length v = n"
      by (auto dest: match_fvi_trm_None[OF sym] arg_cong[of _ _ length])
    ultimately show ?thesis using 3(3)
      by (auto simp: list_eq_iff_nth_eq wf_tuple_def)
  qed
qed (auto simp: wf_tuple_def intro: nth_equalityI)

lemma eq_rel_eval_trm: "v \<in> eq_rel n t1 t2 \<Longrightarrow> is_simple_eq t1 t2 \<Longrightarrow>
  \<forall>x\<in>Formula.fv_trm t1 \<union> Formula.fv_trm t2. x < n \<Longrightarrow>
  Formula.eval_trm (map the v) t1 = Formula.eval_trm (map the v) t2"
  by (cases t1; cases t2) (simp_all add: is_simple_eq_def singleton_table_def split: if_splits)

lemma in_eq_rel: "wf_tuple n (Formula.fv_trm t1 \<union> Formula.fv_trm t2) v \<Longrightarrow>
  is_simple_eq t1 t2 \<Longrightarrow>
  Formula.eval_trm (map the v) t1 = Formula.eval_trm (map the v) t2 \<Longrightarrow>
  v \<in> eq_rel n t1 t2"
  by (cases t1; cases t2)
    (auto simp: is_simple_eq_def singleton_table_def wf_tuple_def unit_table_def
      intro!: nth_equalityI split: if_splits)

lemma table_eq_rel: "is_simple_eq t1 t2 \<Longrightarrow>
  table n (Formula.fv_trm t1 \<union> Formula.fv_trm t2) (eq_rel n t1 t2)"
  by (cases t1; cases t2; simp add: is_simple_eq_def)

lemma wf_tuple_Suc_fviD: "wf_tuple (Suc n) (Formula.fvi b \<phi>) v \<Longrightarrow> wf_tuple n (Formula.fvi (Suc b) \<phi>) (tl v)"
  unfolding wf_tuple_def by (simp add: fvi_Suc nth_tl)

lemma table_fvi_tl: "table (Suc n) (Formula.fvi b \<phi>) X \<Longrightarrow> table n (Formula.fvi (Suc b) \<phi>) (tl ` X)"
  unfolding table_def by (auto intro: wf_tuple_Suc_fviD)

lemma wf_tuple_Suc_fvi_SomeI: "0 \<in> Formula.fvi b \<phi> \<Longrightarrow> wf_tuple n (Formula.fvi (Suc b) \<phi>) v \<Longrightarrow>
  wf_tuple (Suc n) (Formula.fvi b \<phi>) (Some x # v)"
  unfolding wf_tuple_def
  by (auto simp: fvi_Suc less_Suc_eq_0_disj)

lemma wf_tuple_Suc_fvi_NoneI: "0 \<notin> Formula.fvi b \<phi> \<Longrightarrow> wf_tuple n (Formula.fvi (Suc b) \<phi>) v \<Longrightarrow>
  wf_tuple (Suc n) (Formula.fvi b \<phi>) (None # v)"
  unfolding wf_tuple_def
  by (auto simp: fvi_Suc less_Suc_eq_0_disj)

lemma qtable_project_fv: "qtable (Suc n) (fv \<phi>) (mem_restr (lift_envs R)) P X \<Longrightarrow>
    qtable n (Formula.fvi (Suc 0) \<phi>) (mem_restr R)
      (\<lambda>v. \<exists>x. P ((if 0 \<in> fv \<phi> then Some x else None) # v)) (tl ` X)"
  using neq0_conv by (fastforce simp: image_iff Bex_def fvi_Suc elim!: qtable_cong dest!: qtable_project)

lemma mem_restr_lift_envs'_append[simp]:
  "length xs = b \<Longrightarrow> mem_restr (lift_envs' b R) (xs @ ys) = mem_restr R ys"
  unfolding mem_restr_def lift_envs'_def
  by (auto simp: list_all2_append list.rel_map intro!: exI[where x="map the xs"] list.rel_refl)

lemma nth_list_update_alt: "xs[i := x] ! j = (if i < length xs \<and> i = j then x else xs ! j)"
  by auto

lemma wf_tuple_upd_None: "wf_tuple n A xs \<Longrightarrow> A - {i} = B \<Longrightarrow> wf_tuple n B (xs[i:=None])"
  unfolding wf_tuple_def
  by (auto simp: nth_list_update_alt)

lemma mem_restr_upd_None: "mem_restr R xs \<Longrightarrow> mem_restr R (xs[i:=None])"
  unfolding mem_restr_def
  by (auto simp: list_all2_conv_all_nth nth_list_update_alt)

lemma mem_restr_dropI: "mem_restr (lift_envs' b R) xs \<Longrightarrow> mem_restr R (drop b xs)"
  unfolding mem_restr_def lift_envs'_def
  by (auto simp: append_eq_conv_conj list_all2_append2)

lemma mem_restr_dropD:
  assumes "b \<le> length xs" and "mem_restr R (drop b xs)"
  shows "mem_restr (lift_envs' b R) xs"
proof -
  let ?R = "\<lambda>a b. a \<noteq> None \<longrightarrow> a = Some b"
  from assms(2) obtain v where "v \<in> R" and "list_all2 ?R (drop b xs) v"
    unfolding mem_restr_def ..
  show ?thesis unfolding mem_restr_def proof
    have "list_all2 ?R (take b xs) (map the (take b xs))"
      by (auto simp: list.rel_map intro!: list.rel_refl)
    moreover note \<open>list_all2 ?R (drop b xs) v\<close>
    ultimately have "list_all2 ?R (take b xs @ drop b xs) (map the (take b xs) @ v)"
      by (rule list_all2_appendI)
    then show "list_all2 ?R xs (map the (take b xs) @ v)" by simp
    show "map the (take b xs) @ v \<in> lift_envs' b R"
      unfolding lift_envs'_def using assms(1) \<open>v \<in> R\<close> by auto
  qed
qed

lemma wf_tuple_append: "wf_tuple a {x \<in> A. x < a} xs \<Longrightarrow>
  wf_tuple b {x - a | x. x \<in> A \<and> x \<ge> a} ys \<Longrightarrow>
  wf_tuple (a + b) A (xs @ ys)"
  unfolding wf_tuple_def by (auto simp: nth_append eq_diff_iff)

lemma wf_tuple_map_Some: "length xs = n \<Longrightarrow> {0..<n} \<subseteq> A \<Longrightarrow> wf_tuple n A (map Some xs)"
  unfolding wf_tuple_def by auto

lemma wf_tuple_drop: "wf_tuple (b + n) A xs \<Longrightarrow> {x - b | x. x \<in> A \<and> x \<ge> b} = B \<Longrightarrow>
  wf_tuple n B (drop b xs)"
  unfolding wf_tuple_def by force

lemma ecard_image: "inj_on f A \<Longrightarrow> ecard (f ` A) = ecard A"
  unfolding ecard_def by (auto simp: card_image dest: finite_imageD)

lemma meval_trm_eval_trm: "wf_tuple n A x \<Longrightarrow> fv_trm t \<subseteq> A \<Longrightarrow> \<forall>i\<in>A. i < n \<Longrightarrow>
    meval_trm t x = Formula.eval_trm (map the x) t"
  unfolding wf_tuple_def
  by (induction t) simp_all

lemma list_update_id: "xs ! i = z \<Longrightarrow> xs[i:=z] = xs"
  by (induction xs arbitrary: i) (auto split: nat.split)

lemma qtable_wf_tupleD: "qtable n A P Q X \<Longrightarrow> \<forall>x\<in>X. wf_tuple n A x"
  unfolding qtable_def table_def by blast

lemma qtable_eval_agg:
  assumes inner: "qtable (b + n) (Formula.fv \<phi>) (mem_restr (lift_envs' b R))
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel"
    and n: "\<forall>x\<in>Formula.fv (Formula.Agg y \<omega> b f \<phi>). x < n"
    and fresh: "y + b \<notin> Formula.fv \<phi>"
    and b_fv: "{0..<b} \<subseteq> Formula.fv \<phi>"
    and f_fv: "Formula.fv_trm f \<subseteq> Formula.fv \<phi>"
    and g0: "g0 = (Formula.fv \<phi> \<subseteq> {0..<b})"
  shows "qtable n (Formula.fv (Formula.Agg y \<omega> b f \<phi>)) (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> b f \<phi>)) (eval_agg n g0 y \<omega> b f rel)"
    (is "qtable _ ?fv _ ?Q ?rel'")
proof -
  define M where "M = (\<lambda>v. {(x, ecard Zs) | x Zs.
      Zs = {zs. length zs = b \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and>
      Zs \<noteq> {}})"
  have f_fvi: "Formula.fvi_trm b f \<subseteq> Formula.fvi b \<phi>"
    using f_fv by (auto simp: fvi_trm_iff_fv_trm[where b=b] fvi_iff_fv[where b=b])
  show ?thesis proof (cases "g0 \<and> rel = empty_table")
    case True
    then have [simp]: "Formula.fvi b \<phi> = {}"
      by (auto simp: g0 fvi_iff_fv(1)[where b=b])
    then have [simp]: "Formula.fvi_trm b f = {}"
      using f_fvi by auto
    show ?thesis proof (rule qtableI)
      show "table n ?fv ?rel'" by (simp add: eval_agg_def True)
    next
      fix v
      assume "wf_tuple n ?fv v" "mem_restr R v"
      have "\<not> Formula.sat \<sigma> V (zs @ map the v) i \<phi>" if [simp]: "length zs = b" for zs
      proof -
        let ?zs = "map2 (\<lambda>z i. if i \<in> Formula.fv \<phi> then Some z else None) zs [0..<b]"
        have "wf_tuple b {x \<in> fv \<phi>. x < b} ?zs"
          by (simp add: wf_tuple_def)
        then have "wf_tuple (b + n) (Formula.fv \<phi>) (?zs @ v[y:=None])"
          using \<open>wf_tuple n ?fv v\<close> True
          by (auto simp: g0 intro!: wf_tuple_append wf_tuple_upd_None)
        then have "\<not> Formula.sat \<sigma> V (map the (?zs @ v[y:=None])) i \<phi>"
          using True \<open>mem_restr R v\<close>
          by (auto simp del: map_append dest!: in_qtableI[OF inner, rotated -1]
              intro!: mem_restr_upd_None)
        also have "Formula.sat \<sigma> V (map the (?zs @ v[y:=None])) i \<phi> \<longleftrightarrow> Formula.sat \<sigma> V (zs @ map the v) i \<phi>"
          using True by (auto simp: g0 nth_append intro!: sat_fv_cong)
        finally show ?thesis .
      qed
      then have M_empty: "M (map the v) = {}"
        unfolding M_def by blast
      show "Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> b f \<phi>)"
        if "v \<in> eval_agg n g0 y \<omega> b f rel"
        using M_empty True that n
        by (simp add: M_def eval_agg_def g0 singleton_table_def)
      have "v \<in> singleton_table n y (the (v ! y))" "length v = n"
        using \<open>wf_tuple n ?fv v\<close> unfolding wf_tuple_def singleton_table_def
        by (auto simp add: tabulate_alt map_nth
            intro!: trans[OF map_cong[where g="(!) v", simplified nth_map, OF refl], symmetric])
      then show "v \<in> eval_agg n g0 y \<omega> b f rel"
        if "Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> b f \<phi>)"
        using M_empty True that n
        by (simp add: M_def eval_agg_def g0)
    qed
  next
    case non_default_case: False
    have union_fv: "{0..<b} \<union> (\<lambda>x. x + b) ` Formula.fvi b \<phi> = fv \<phi>"
      using b_fv
      by (auto simp: fvi_iff_fv(1)[where b=b] intro!: image_eqI[where b=x and x="x - b" for x])
    have b_n: "\<forall>x\<in>fv \<phi>. x < b + n"
    proof
      fix x assume "x \<in> fv \<phi>"
      show "x < b + n" proof (cases "x \<ge> b")
        case True
        with \<open>x \<in> fv \<phi>\<close> have "x - b \<in> ?fv"
          by (simp add: fvi_iff_fv(1)[where b=b])
        then show ?thesis using n f_fvi by (auto simp: Un_absorb2)
      qed simp
    qed

    define M' where "M' = (\<lambda>k. let group = Set.filter (\<lambda>x. drop b x = k) rel;
        images = meval_trm f ` group
      in (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` images)"
    have M'_M: "M' (drop b x) = M (map the (drop b x))" if "x \<in> rel" "mem_restr (lift_envs' b R) x" for x
    proof -
      from that have wf_x: "wf_tuple (b + n) (fv \<phi>) x"
        by (auto elim!: in_qtableE[OF inner])
      then have wf_zs_x: "wf_tuple (b + n) (fv \<phi>) (map Some zs @ drop b x)"
        if "length zs = b" for zs
        using that b_fv
        by (auto intro!: wf_tuple_append wf_tuple_map_Some wf_tuple_drop)
      have 1: "(length zs = b \<and> Formula.sat \<sigma> V (zs @ map the (drop b x)) i \<phi> \<and>
          Formula.eval_trm (zs @ map the (drop b x)) f = y) \<longleftrightarrow>
        (\<exists>a. a \<in> rel \<and> take b a = map Some zs \<and> drop b a = drop b x \<and> meval_trm f a = y)"
        (is "?A \<longleftrightarrow> (\<exists>a. ?B a)") for y zs
      proof (intro iffI conjI)
        assume ?A
        then have "?B (map Some zs @ drop (length zs) x)"
          using in_qtableI[OF inner wf_zs_x] \<open>mem_restr (lift_envs' b R) x\<close>
            meval_trm_eval_trm[OF wf_zs_x f_fv b_n]
          by (auto intro!: mem_restr_dropI)
        then show "\<exists>a. ?B a" ..
      next
        assume "\<exists>a. ?B a"
        then obtain a where "?B a" ..
        then have "a \<in> rel" and a_eq: "a = map Some zs @ drop b x"
          using append_take_drop_id[of b a] by auto
        then have "length a = b + n"
          using inner unfolding qtable_def table_def
          by (blast intro!: wf_tuple_length)
        then show "length zs = b"
          using wf_tuple_length[OF wf_x] unfolding a_eq by simp
        then have "mem_restr (lift_envs' b R) a"
          using \<open>mem_restr _ x\<close> unfolding a_eq by (auto intro!: mem_restr_dropI)
        then show "Formula.sat \<sigma> V (zs @ map the (drop b x)) i \<phi>"
          using in_qtableE[OF inner \<open>a \<in> rel\<close>]
          by (auto simp: a_eq sat_fv_cong[THEN iffD1, rotated -1])
        from \<open>?B a\<close> show "Formula.eval_trm (zs @ map the (drop b x)) f = y"
          using meval_trm_eval_trm[OF wf_zs_x f_fv b_n, OF \<open>length zs = b\<close>]
          unfolding a_eq by simp
      qed
      have 2: "map Some (map the (take b a)) = take b a" if "a \<in> rel" for a
        using that b_fv inner[THEN qtable_wf_tupleD]
        unfolding table_def wf_tuple_def
        by (auto simp: list_eq_iff_nth_eq)
      have 3: "ecard {zs. \<exists>a. a \<in> rel \<and> take b a = map Some zs \<and> drop b a = drop b x \<and> P a} =
        ecard {a. a \<in> rel \<and> drop b a = drop b x \<and> P a}" (is "ecard ?A = ecard ?B") for P
      proof -
        have "ecard ?A = ecard ((\<lambda>zs. map Some zs @ drop b x) ` ?A)"
          by (auto intro!: ecard_image[symmetric] inj_onI)
        also have "(\<lambda>zs. map Some zs @ drop b x) ` ?A = ?B"
          by (subst (1 2) eq_commute) (auto simp: image_iff, metis "2" append_take_drop_id)
        finally show ?thesis .
      qed
      show ?thesis
        unfolding M_def M'_def
        by (auto simp: non_default_case Let_def image_def Set.filter_def 1 3, metis "2")
    qed
    have drop_lift: "mem_restr (lift_envs' b R) x" if "x \<in> rel" "mem_restr R ((drop b x)[y:=z])" for x z
    proof -
      have "(drop b x)[y:=None] = (drop b x)[y:=drop b x ! y]" proof -
        from \<open>x \<in> rel\<close> have "drop b x ! y = None"
          using fresh n inner[THEN qtable_wf_tupleD]
          by (simp add: add.commute wf_tuple_def)
        then show ?thesis by simp
      qed
      then have "(drop b x)[y:=None] = drop b x" by simp
      moreover from \<open>x \<in> rel\<close> have "length x = b + n"
        using inner[THEN qtable_wf_tupleD]
        by (simp add: wf_tuple_def)
      moreover from that(2) have "mem_restr R ((drop b x)[y:=z, y:=None])"
        by (rule mem_restr_upd_None)
      ultimately show ?thesis
        by (auto intro!: mem_restr_dropD)
    qed

    {
      fix v
      assume "mem_restr R v"
      have "v \<in> (\<lambda>k. k[y:=Some (eval_agg_op \<omega> (M' k))]) ` drop b ` rel \<longleftrightarrow>
          v \<in> (\<lambda>k. k[y:=Some (eval_agg_op \<omega> (M (map the k)))]) ` drop b ` rel"
        (is "v \<in> ?A \<longleftrightarrow> v \<in> ?B")
      proof
        assume "v \<in> ?A"
        then obtain v' where *: "v' \<in> rel" "v = (drop b v')[y:=Some (eval_agg_op \<omega> (M' (drop b v')))]"
          by auto
        then have "M' (drop b v') = M (map the (drop b v'))"
          using \<open>mem_restr R v\<close> by (auto intro!: M'_M drop_lift)
        with * show "v \<in> ?B" by simp
      next
        assume "v \<in> ?B"
        then obtain v' where *: "v' \<in> rel" "v = (drop b v')[y:=Some (eval_agg_op \<omega> (M (map the (drop b v'))))]"
          by auto
        then have "M (map the (drop b v')) = M' (drop b v')"
          using \<open>mem_restr R v\<close> by (auto intro!: M'_M[symmetric] drop_lift)
        with * show "v \<in> ?A" by simp
      qed
      then have "v \<in> eval_agg n g0 y \<omega> b f rel \<longleftrightarrow> v \<in> (\<lambda>k. k[y:=Some (eval_agg_op \<omega> (M (map the k)))]) ` drop b ` rel"
        by (simp add: non_default_case eval_agg_def M'_def Let_def)
    }
    note alt = this

    show ?thesis proof (rule qtableI)
      show "table n ?fv ?rel'"
        using inner[THEN qtable_wf_tupleD] n f_fvi
        by (auto simp: eval_agg_def non_default_case table_def wf_tuple_def Let_def nth_list_update
            fvi_iff_fv[where b=b] add.commute)
    next
      fix v
      assume "wf_tuple n ?fv v" "mem_restr R v"
      then have length_v: "length v = n" by (simp add: wf_tuple_def)

      show "Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> b f \<phi>)"
        if "v \<in> eval_agg n g0 y \<omega> b f rel"
      proof -
        from that obtain v' where "v' \<in> rel"
          "v = (drop b v')[y:=Some (eval_agg_op \<omega> (M (map the (drop b v'))))]"
          using alt[OF \<open>mem_restr R v\<close>] by blast
        then have length_v': "length v' = b + n"
          using inner[THEN qtable_wf_tupleD]
          by (simp add: wf_tuple_def)
        have "Formula.sat \<sigma> V (map the v') i \<phi>"
          using \<open>v' \<in> rel\<close> \<open>mem_restr R v\<close>
          by (auto simp: \<open>v = _\<close> elim!: in_qtableE[OF inner] intro!: drop_lift \<open>v' \<in> rel\<close>)
        then have "Formula.sat \<sigma> V (map the (take b v') @ map the v) i \<phi>"
        proof (rule sat_fv_cong[THEN iffD1, rotated], intro ballI)
          fix x
          assume "x \<in> fv \<phi>"
          then have "x \<noteq> y + b" using fresh by blast
          moreover have "x < length v'"
            using \<open>x \<in> fv \<phi>\<close> b_n by (simp add: length_v')
          ultimately show "map the v' ! x = (map the (take b v') @ map the v) ! x"
            by (auto simp: \<open>v = _\<close> nth_append)
        qed
        then have 1: "M (map the v) \<noteq> {}" by (force simp: M_def length_v')

        have "y < length (drop b v')" using n by (simp add: length_v')
        moreover have "Formula.sat \<sigma> V (zs @ map the v) i \<phi> \<longleftrightarrow>
          Formula.sat \<sigma> V (zs @ map the (drop b v')) i \<phi>" if "length zs = b" for zs
        proof (intro sat_fv_cong ballI)
          fix x
          assume "x \<in> fv \<phi>"
          then have "x \<noteq> y + b" using fresh by blast
          moreover have "x < length v'"
            using \<open>x \<in> fv \<phi>\<close> b_n by (simp add: length_v')
          ultimately show "(zs @ map the v) ! x = (zs @ map the (drop b v')) ! x"
            by (auto simp: \<open>v = _\<close> that nth_append)
        qed
        moreover have "Formula.eval_trm (zs @ map the v) f =
          Formula.eval_trm (zs @ map the (drop b v')) f" if "length zs = b" for zs
        proof (intro eval_trm_fv_cong ballI)
          fix x
          assume "x \<in> fv_trm f"
          then have "x \<noteq> y + b" using f_fv fresh by blast
          moreover have "x < length v'"
            using \<open>x \<in> fv_trm f\<close> f_fv b_n by (auto simp: length_v')
          ultimately show "(zs @ map the v) ! x = (zs @ map the (drop b v')) ! x"
            by (auto simp: \<open>v = _\<close> that nth_append)
        qed
        ultimately have "map the v ! y = eval_agg_op \<omega> (M (map the v))"
          by (simp add: M_def \<open>v = _\<close> conj_commute cong: conj_cong)
        with 1 show ?thesis by (auto simp: M_def)
      qed

      show "v \<in> eval_agg n g0 y \<omega> b f rel"
        if sat_Agg: "Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> b f \<phi>)"
      proof -
        obtain zs where "length zs = b" and "map Some zs @ v[y:=None] \<in> rel"
        proof (cases "fv \<phi> \<subseteq> {0..<b}")
          case True
          with non_default_case have "rel \<noteq> empty_table" by (simp add: g0)
          then obtain x where "x \<in> rel" by auto
          have "(\<forall>i < n. (v[y:=None]) ! i = None)"
            using True \<open>wf_tuple n ?fv v\<close> f_fv
            by (fastforce simp: wf_tuple_def fvi_iff_fv[where b=b] fvi_trm_iff_fv_trm[where b=b])
          moreover have x: "(\<forall>i < n. drop b x ! i = None) \<and> length x = b + n"
            using True \<open>x \<in> rel\<close> inner[THEN qtable_wf_tupleD] f_fv
            by (auto simp: wf_tuple_def)
          ultimately have "v[y:=None] = drop b x"
            unfolding list_eq_iff_nth_eq by (auto simp: length_v)
          with \<open>x \<in> rel\<close> have "take b x @ v[y:=None] \<in> rel" by simp
          moreover have "map (Some \<circ> the) (take b x) = take b x"
            using True \<open>x \<in> rel\<close> inner[THEN qtable_wf_tupleD] b_fv
            by (subst map_cong[where g=id, OF refl]) (auto simp: wf_tuple_def in_set_conv_nth)
          ultimately have "map Some (map the (take b x)) @ v[y:=None] \<in> rel" by simp
          then show thesis using x[THEN conjunct2] by (fastforce intro!: that[rotated])
        next
          case False
          with sat_Agg obtain zs where "length zs = b" and "Formula.sat \<sigma> V (zs @ map the v) i \<phi>"
            by auto
          then have "Formula.sat \<sigma> V (zs @ map the (v[y:=None])) i \<phi>"
            using fresh
            by (auto simp: map_update not_less nth_append elim!: sat_fv_cong[THEN iffD1, rotated]
                intro!: nth_list_update_neq[symmetric])
          then have "map Some zs @ v[y:=None] \<in> rel"
            using b_fv f_fv fresh
            by (auto intro!: in_qtableI[OF inner] wf_tuple_append wf_tuple_map_Some
                wf_tuple_upd_None \<open>wf_tuple n ?fv v\<close> mem_restr_upd_None \<open>mem_restr R v\<close>
                simp: \<open>length zs = b\<close> set_eq_iff fvi_iff_fv[where b=b] fvi_trm_iff_fv_trm[where b=b])
              force+
          with that \<open>length zs = b\<close> show thesis by blast
        qed
        then have 1: "v[y:=None] \<in> drop b ` rel" by (intro image_eqI) auto

        have y_length: "y < length v" using n by (simp add: length_v)
        moreover have "Formula.sat \<sigma> V (zs @ map the (v[y:=None])) i \<phi> \<longleftrightarrow>
          Formula.sat \<sigma> V (zs @ map the v) i \<phi>" if "length zs = b" for zs
        proof (intro sat_fv_cong ballI)
          fix x
          assume "x \<in> fv \<phi>"
          then have "x \<noteq> y + b" using fresh by blast
          moreover have "x < b + length v"
            using \<open>x \<in> fv \<phi>\<close> b_n by (simp add: length_v)
          ultimately show "(zs @ map the (v[y:=None])) ! x = (zs @ map the v) ! x"
            by (auto simp: that nth_append)
        qed
        moreover have "Formula.eval_trm (zs @ map the (v[y:=None])) f =
          Formula.eval_trm (zs @ map the v) f" if "length zs = b" for zs
        proof (intro eval_trm_fv_cong ballI)
          fix x
          assume "x \<in> fv_trm f"
          then have "x \<noteq> y + b" using f_fv fresh by blast
          moreover have "x < b + length v"
            using \<open>x \<in> fv_trm f\<close> f_fv b_n by (auto simp: length_v)
          ultimately show "(zs @ map the (v[y:=None])) ! x = (zs @ map the v) ! x"
            by (auto simp: that nth_append)
        qed
        ultimately have "map the v ! y = eval_agg_op \<omega> (M (map the (v[y:=None])))"
          using sat_Agg by (simp add: M_def cong: conj_cong) (simp cong: rev_conj_cong)
        then have 2: "v ! y = Some (eval_agg_op \<omega> (M (map the (v[y:=None]))))"
          using \<open>wf_tuple n ?fv v\<close> y_length by (auto simp add: wf_tuple_def)
        show ?thesis
          unfolding alt[OF \<open>mem_restr R v\<close>]
          by (rule image_eqI[where x="v[y:=None]"]) (use 1 2 in \<open>auto simp: y_length list_update_id\<close>)
      qed
    qed
  qed
qed

lemma mprev_next_NilE[elim!]: "mprev_next I xs ts = (ys, [], []) \<Longrightarrow>
  (xs = [] \<Longrightarrow> ts = [] \<Longrightarrow> ys = [] \<Longrightarrow> R) \<Longrightarrow> R"
  by (induct I xs ts arbitrary: ys rule: mprev_next.induct) (auto split: prod.splits)

lemma mprev: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> i \<le> j' \<Longrightarrow> i \<le> j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then P i X else X = empty_table)
    [i..<min j' (if i = j then j else j-1)] ys \<and>
  list_all2 P [min j' (if i = j then j else j-1)..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min j' (if i = j then j else j-1)..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min j' (if i = j then j else j-1) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min j' (j-1) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(1)[of "tl ys" xs' ts' "Suc i"] 4(2-6) show ?case
    by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv Suc_less_eq2
        elim!: list.rel_mono_strong split: prod.splits if_splits)
qed (auto simp: gr0_conv_Suc)

lemma mnext: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [Suc i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> Suc i \<le> j' \<Longrightarrow> i \<le> j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then P (Suc i) X else X = empty_table)
    [i..<min (j'-1) ((if i = j then j else j-1))] ys \<and>
  list_all2 P [Suc (min (j'-1) ((if i = j then j else j-1)))..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (j'-1) ((if i = j then j else j-1))..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min (j' - 1) ((if i = j then j else j-1)) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min (j' - 1) ((if i = j then j else j-1)) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(1)[of "tl ys" xs' ts' "Suc i"] 4(2-6) show ?case
    by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv Suc_less_eq2
        elim!: list.rel_mono_strong split: prod.splits if_splits) (* slow 10 sec *)
qed auto

lemma in_foldr_UnI: "x \<in> A \<Longrightarrow> A \<in> set xs \<Longrightarrow> x \<in> foldr (\<union>) xs {}"
  by (induction xs) auto

lemma in_foldr_UnE: "x \<in> foldr (\<union>) xs {} \<Longrightarrow> (\<And>A. A \<in> set xs \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction xs) auto

lemma sat_the_restrict: "fv \<phi> \<subseteq> A \<Longrightarrow> Formula.sat \<sigma> V (map the (restrict A v)) i \<phi> = Formula.sat \<sigma> V (map the v) i \<phi>"
  by (rule sat_fv_cong) (auto intro!: map_the_restrict)

lemma eps_the_restrict: "fv_regex r \<subseteq> A \<Longrightarrow> Regex.eps (Formula.sat \<sigma> V (map the (restrict A v))) i r = Regex.eps (Formula.sat \<sigma> V (map the v)) i r"
  by (rule eps_fv_cong) (auto intro!: map_the_restrict)

lemma sorted_wrt_filter[simp]: "sorted_wrt R xs \<Longrightarrow> sorted_wrt R (filter P xs)"
  by (induct xs) auto

lemma concat_map_filter[simp]:
  "concat (map f (filter P xs)) = concat (map (\<lambda>x. if P x then f x else []) xs)"
  by (induct xs) auto

lemma map_filter_alt:
  "map f (filter P xs) = concat (map (\<lambda>x. if P x then [f x] else []) xs)"
  by (induct xs) auto

lemma (in maux) update_since:
  assumes pre: "wf_since_aux \<sigma> V R args \<phi> \<psi> aux ne"
    and qtable1: "qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne \<phi>) rel1"
    and qtable2: "qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne \<psi>) rel2"
    and result_eq: "(rel, aux') = update_since args rel1 rel2 (\<tau> \<sigma> ne) aux"
    and fvi_subset: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>"
    and args_R: "args_R args = Formula.fv \<psi>"
    and args_pos: "args_pos args = pos"
  shows "wf_since_aux \<sigma> V R args \<phi> \<psi> aux' (Suc ne)"
    and "qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Sincep pos \<phi> I \<psi>)) rel"
proof -
  let ?wf_tuple = "\<lambda>v. wf_tuple n (Formula.fv \<psi>) v"
  note sat.simps[simp del]
  from pre[unfolded wf_since_aux_def] obtain cur auxlist where aux: "valid_msaux args cur aux auxlist"
    "sorted_wrt (\<lambda>x y. fst y < fst x) auxlist"
    "\<And>t X. (t, X) \<in> set auxlist \<Longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne - 1) \<and> memR I (\<tau> \<sigma> (ne - 1) - t) \<and>
      (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (fv \<psi>) (mem_restr R)
        (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne - 1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne - 1) - t)) \<psi>)) X"
    "\<And>t. ne \<noteq> 0 \<Longrightarrow> t \<le> \<tau> \<sigma> (ne - 1) \<Longrightarrow> memR I (\<tau> \<sigma> (ne - 1) - t) \<Longrightarrow> (\<exists>i. \<tau> \<sigma> i = t) \<Longrightarrow>
      (\<exists>X. (t, X) \<in> set auxlist)"
    and cur_def:
    "cur = (if ne = 0 then 0 else \<tau> \<sigma> (ne - 1))"
    unfolding args_ivl args_n args_pos by blast
  from pre[unfolded wf_since_aux_def] have fv_sub: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>" by simp

  define aux0 where "aux0 = join_msaux args rel1 (add_new_ts_msaux args (\<tau> \<sigma> ne) aux)"
  define auxlist0 where "auxlist0 = [(t, join rel pos rel1). (t, rel) \<leftarrow> auxlist, memR I (\<tau> \<sigma> ne - t)]"
  have tabL: "table (args_n args) (args_L args) rel1"
    using qtable1[unfolded qtable_def] unfolding args_n[symmetric] args_L[symmetric] by simp
  have cur_le: "cur \<le> \<tau> \<sigma> ne"
    unfolding cur_def by auto
  have valid0: "valid_msaux args (\<tau> \<sigma> ne) aux0 auxlist0" unfolding aux0_def auxlist0_def
    using valid_join_msaux[OF valid_add_new_ts_msaux[OF aux(1)], OF cur_le tabL]
    by (auto simp: args_ivl args_pos cur_def map_filter_alt split_beta cong: map_cong)
  from aux(2) have sorted_auxlist0: "sorted_wrt (\<lambda>x y. fst x > fst y) auxlist0"
    unfolding auxlist0_def
    by (induction auxlist) (auto simp add: sorted_wrt_append)
  have in_auxlist0_1: "(t, X) \<in> set auxlist0 \<Longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> ne - t) \<and>
      (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. (Formula.sat \<sigma> V (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>) \<and>
        (if pos then Formula.sat \<sigma> V (map the v) ne \<phi> else \<not> Formula.sat \<sigma> V (map the v) ne \<phi>))) X" for t X
    unfolding auxlist0_def using fvi_subset
    by (auto 0 1 elim!: qtable_join[OF _ qtable1] simp: sat_the_restrict dest!: aux(3))
  then have in_auxlist0_le_\<tau>: "(t, X) \<in> set auxlist0 \<Longrightarrow> t \<le> \<tau> \<sigma> ne" for t X
    by (meson \<tau>_mono diff_le_self le_trans)
  have in_auxlist0_2: "ne \<noteq> 0 \<Longrightarrow> t \<le> \<tau> \<sigma> (ne-1) \<Longrightarrow> memR I (\<tau> \<sigma> ne - t) \<Longrightarrow> \<exists>i. \<tau> \<sigma> i = t \<Longrightarrow>
    \<exists>X. (t, X) \<in> set auxlist0" for t
  proof -
    fix t
    assume "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne-1)" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t"
    then obtain X where "(t, X) \<in> set auxlist"
      by (atomize_elim, intro aux(4))
        (auto simp: gr0_conv_Suc elim!: order_trans[rotated] intro!: diff_le_mono \<tau>_mono)
    with \<open>memR I (\<tau> \<sigma> ne - t)\<close> have "(t, join X pos rel1) \<in> set auxlist0"
      unfolding auxlist0_def by (auto elim!: bexI[rotated] intro!: exI[of _ X])
    then show "\<exists>X. (t, X) \<in> set auxlist0"
      by blast
  qed
  have auxlist0_Nil: "auxlist0 = [] \<Longrightarrow> ne = 0 \<or> ne \<noteq> 0 \<and> (\<forall>t. t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> ne - t) \<longrightarrow>
        (\<nexists>i. \<tau> \<sigma> i = t))"
    using in_auxlist0_2 by (auto)

  have aux'_eq: "aux' = add_new_table_msaux args rel2 aux0"
    using result_eq unfolding aux0_def update_since_def Let_def by simp
  define auxlist' where
    auxlist'_eq: "auxlist' = (case auxlist0 of
      [] \<Rightarrow> [(\<tau> \<sigma> ne, rel2)]
    | x # auxlist' \<Rightarrow> (if fst x = \<tau> \<sigma> ne then (fst x, snd x \<union> rel2) # auxlist' else (\<tau> \<sigma> ne, rel2) # x # auxlist'))"
  have tabR: "table (args_n args) (args_R args) rel2"
    using qtable2[unfolded qtable_def] unfolding args_n[symmetric] args_R[symmetric] by simp
  have valid': "valid_msaux args (\<tau> \<sigma> ne) aux' auxlist'"
    unfolding aux'_eq auxlist'_eq using valid_add_new_table_msaux[OF valid0 tabR]
    by (auto simp: not_le split: list.splits option.splits if_splits)
  have sorted_auxlist': "sorted_wrt (\<lambda>x y. fst x > fst y) auxlist'"
    unfolding auxlist'_eq
    using sorted_auxlist0 in_auxlist0_le_\<tau> by (cases auxlist0) fastforce+
  have in_auxlist'_1: "t \<le> \<tau> \<sigma> ne \<and> memR I (\<tau> \<sigma> ne - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Sincep pos \<phi> (point (\<tau> \<sigma> ne - t)) \<psi>)) X"
    if auxlist': "(t, X) \<in> set auxlist'" for t X
  proof (cases auxlist0)
    case Nil
    with auxlist' show ?thesis
      unfolding auxlist'_eq using qtable2 auxlist0_Nil
      by (auto simp: zero_enat_def[symmetric] sat_Since_rec[where i=ne]
          dest: spec[of _ "\<tau> \<sigma> (ne-1)"] elim!: qtable_cong[OF _ refl])
  next
    case (Cons a as)
    show ?thesis
    proof (cases "t = \<tau> \<sigma> ne")
      case t: True
      show ?thesis
      proof (cases "fst a = \<tau> \<sigma> ne")
        case True
        with auxlist' Cons t have "X = snd a \<union> rel2"
          unfolding auxlist'_eq using sorted_auxlist0 by (auto split: if_splits)
        moreover from in_auxlist0_1[of "fst a" "snd a"] Cons have "ne \<noteq> 0"
          "fst a \<le> \<tau> \<sigma> (ne - 1)" "memR I (\<tau> \<sigma> ne - fst a)" "\<exists>i. \<tau> \<sigma> i = fst a"
          "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne - 1)
            (Sincep pos \<phi> (point (\<tau> \<sigma> (ne - 1) - fst a)) \<psi>) \<and> (if pos then Formula.sat \<sigma> V (map the v) ne \<phi>
              else \<not> Formula.sat \<sigma> V (map the v) ne \<phi>)) (snd a)"
          by (auto simp: True[symmetric] zero_enat_def[symmetric])
        ultimately show ?thesis using qtable2 t True
          by (auto simp: sat_Since_rec[where i=ne] sat.simps(6) elim!: qtable_union)
      next
        case False
        with auxlist' Cons t have "X = rel2"
          unfolding auxlist'_eq using sorted_auxlist0 in_auxlist0_le_\<tau>[of "fst a" "snd a"] by (auto split: if_splits)
        with auxlist' Cons t False show ?thesis
          unfolding auxlist'_eq using qtable2 in_auxlist0_2[of "\<tau> \<sigma> (ne-1)"] in_auxlist0_le_\<tau>[of "fst a" "snd a"] sorted_auxlist0
          by (auto simp: sat_Since_rec[where i=ne] sat.simps(3) zero_enat_def[symmetric] enat_0_iff not_le
              elim!: qtable_cong[OF _ refl] dest!: le_\<tau>_less meta_mp)
      qed
    next
      case False
      with auxlist' Cons have "(t, X) \<in> set auxlist0"
        unfolding auxlist'_eq by (auto split: if_splits)
      then have "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne - 1)" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t"
        "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne - 1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne - 1) - t)) \<psi>) \<and>
           (if pos then Formula.sat \<sigma> V (map the v) ne \<phi> else \<not> Formula.sat \<sigma> V (map the v) ne \<phi>)) X"
        using in_auxlist0_1 by blast+
      with False auxlist' Cons show ?thesis
        unfolding auxlist'_eq using qtable2
        by (fastforce simp: sat_Since_rec[where i=ne] sat.simps(6)
            diff_diff_right[where i="\<tau> \<sigma> ne" and j="\<tau> \<sigma> _ + \<tau> \<sigma> ne" and k="\<tau> \<sigma> (ne - 1)",
              OF trans_le_add2, simplified] elim!: qtable_cong[OF _ refl] order_trans dest: le_\<tau>_less)
    qed
  qed

  have in_auxlist'_2: "\<exists>X. (t, X) \<in> set auxlist'" if "t \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t" for t
  proof (cases "t = \<tau> \<sigma> ne")
    case True
    then show ?thesis
    proof (cases auxlist0)
      case Nil
      with True show ?thesis unfolding auxlist'_eq by (simp add: zero_enat_def[symmetric])
    next
      case (Cons a as)
      with True show ?thesis unfolding auxlist'_eq
        by (cases "fst a = \<tau> \<sigma> ne") (auto simp: zero_enat_def[symmetric])
    qed
  next
    case False
    with that have "ne \<noteq> 0"
      using le_\<tau>_less neq0_conv by blast
    moreover from False that have  "t \<le> \<tau> \<sigma> (ne-1)"
      by (metis One_nat_def Suc_leI Suc_pred \<tau>_mono diff_is_0_eq' order.antisym neq0_conv not_le)
    ultimately obtain X where "(t, X) \<in> set auxlist0" using \<open>memR I (\<tau> \<sigma> ne - t)\<close> \<open>\<exists>i. \<tau> \<sigma> i = t\<close>
      using \<tau>_mono[of "ne - 1" "ne" \<sigma>] by (atomize_elim) (auto intro!: in_auxlist0_2 simp del: \<tau>_mono)
    then show ?thesis unfolding auxlist'_eq using False \<open>memR I (\<tau> \<sigma> ne - t)\<close>
      by (auto intro: exI[of _ X] split: list.split)
  qed

  show "wf_since_aux \<sigma> V R args \<phi> \<psi> aux' (Suc ne)"
    unfolding wf_since_aux_def args_ivl args_n args_pos
    by (auto simp add: fv_sub dest: in_auxlist'_1 intro: sorted_auxlist' in_auxlist'_2
        intro!: exI[of _ auxlist'] valid')

  have "rel = result_msaux args aux'"
    using result_eq by (auto simp add: update_since_def Let_def)
  with valid' have rel_eq: "rel = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist', memL I (\<tau> \<sigma> ne - t)] {}"
    by (auto simp add: args_ivl valid_result_msaux
        intro!: arg_cong[where f = "\<lambda>x. foldr (\<union>) (concat x) {}"] split: option.splits)
  have rel_alt: "rel = (\<Union>(t, rel) \<in> set auxlist'. if memL I (\<tau> \<sigma> ne - t) then rel else empty_table)"
    unfolding rel_eq
    by (auto elim!: in_foldr_UnE bexI[rotated] intro!: in_foldr_UnI)
  show "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Sincep pos \<phi> I \<psi>)) rel"
    unfolding rel_alt
  proof (rule qtable_Union[where Qi="\<lambda>(t, X) v.
    memL I (\<tau> \<sigma> ne - t) \<and> Formula.sat \<sigma> V (map the v) ne (Sincep pos \<phi> (point (\<tau> \<sigma> ne - t)) \<psi>)"],
        goal_cases finite qtable equiv)
    case (equiv v)
    show ?case
    proof (rule iffI, erule sat_Since_point, goal_cases left right)
      case (left j)
      then show ?case using in_auxlist'_2[of "\<tau> \<sigma> j", OF _ _ exI, OF _ _ refl] by auto
    next
      case right
      then show ?case by (auto elim!: sat_Since_pointD dest: in_auxlist'_1)
    qed
  qed (auto dest!: in_auxlist'_1 intro!: qtable_empty)
qed

lemma fv_regex_from_mregex:
  "ok (length \<phi>s) mr \<Longrightarrow> fv_regex (from_mregex mr \<phi>s) \<subseteq> (\<Union>\<phi> \<in> set \<phi>s. fv \<phi>)"
  by (induct mr) (auto simp: Bex_def in_set_conv_nth)+

lemma qtable_\<epsilon>_lax:
  assumes "ok (length \<phi>s) mr"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel) \<phi>s rels"
    and "fv_regex (from_mregex mr \<phi>s) \<subseteq> A" and "qtable n A (mem_restr R) Q guard"
  shows "qtable n A (mem_restr R)
   (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (map the v)) i (from_mregex mr \<phi>s) \<and> Q v) (\<epsilon>_lax guard rels mr)"
  using assms
proof (induct mr)
  case (MPlus mr1 mr2)
  from MPlus(3-6) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  then have "fv_regex (from_mregex mr1 \<phi>s) \<subseteq> A" "fv_regex (from_mregex mr2 \<phi>s) \<subseteq> A"
    using fv_regex_from_mregex[of \<phi>s mr1] fv_regex_from_mregex[of \<phi>s mr2] by (auto simp: subset_eq)
  with MTimes(3-6) show ?case
    by (auto simp: eps_the_restrict restrict_idle intro!: qtable_join[OF MTimes(1,2)])
qed (auto split: prod.splits if_splits simp: qtable_empty_iff list_all2_conv_all_nth
    in_set_conv_nth restrict_idle sat_the_restrict
    intro: in_qtableI qtableI elim!: qtable_join[where A=A and C=A])

lemma nullary_qtable_cases: "qtable n {} P Q X \<Longrightarrow> (X = empty_table \<or> X = unit_table n)"
  by (simp add: qtable_def table_empty)

lemma wf_tuple_unit_table: "wf_tuple n {} x = (x = replicate n None)"
  unfolding wf_tuple_def
  by (metis empty_iff length_replicate nth_equalityI nth_replicate)

lemma qtable_empty_unit_table:
  "qtable n {} R P empty_table \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) (unit_table n)"
  by (auto intro: qtable_unit_table simp add: qtable_empty_iff)

lemma qtable_unit_empty_table:
  "qtable n {} R P (unit_table n) \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) empty_table"
  by (auto intro!: qtable_empty elim: in_qtableE simp add: wf_tuple_empty unit_table_def)

lemma qtable_nonempty_empty_table:
  "qtable n {} R P X \<Longrightarrow> x \<in> X \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) empty_table"
  by (frule nullary_qtable_cases) (auto dest: qtable_unit_empty_table)


lemma qtable_r\<epsilon>_strict:
  assumes "safe_regex Past Strict (from_mregex mr \<phi>s)" "ok (length \<phi>s) mr" "A = fv_regex (from_mregex mr \<phi>s)"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel) \<phi>s rels"
  shows "qtable n A (mem_restr R) (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (map the v)) i (from_mregex mr \<phi>s)) (r\<epsilon>_strict n rels mr)"
  using assms
proof (hypsubst, induct Past Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case (Skip n)
  then show ?case
    by (cases mr) (auto simp: qtable_empty_iff qtable_unit_table split: if_splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) (auto simp: list_all2_conv_all_nth qtable_empty_unit_table
        dest!: qtable_nonempty_empty_table split: if_splits)
next
  case (Plus r s)
  then show ?case
    by (cases mr) (fastforce intro: qtable_union split: if_splits)+
next
  case (TimesP r s)
  then show ?case
    by (cases mr) (auto intro: qtable_cong[OF qtable_\<epsilon>_lax] split: if_splits)+
next
  case (Star r)
  then show ?case
    by (cases mr) (auto simp: qtable_unit_table split: if_splits)
qed

lemma qtable_l\<epsilon>_strict:
  assumes "safe_regex Futu Strict (from_mregex mr \<phi>s)" "ok (length \<phi>s) mr" "A = fv_regex (from_mregex mr \<phi>s)"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel) \<phi>s rels"
  shows "qtable n A (mem_restr R) (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (map the v)) i (from_mregex mr \<phi>s)) (l\<epsilon>_strict n rels mr)"
  using assms
proof (hypsubst, induct Futu Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case (Skip n)
  then show ?case
    by (cases mr) (auto simp: qtable_empty_iff qtable_unit_table split: if_splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) (auto simp: list_all2_conv_all_nth qtable_empty_unit_table
        dest!: qtable_nonempty_empty_table split: if_splits)
next
  case (Plus r s)
  then show ?case
    by (cases mr) (fastforce intro: qtable_union split: if_splits)+
next
  case (TimesF r s)
  then show ?case
    by (cases mr) (auto intro: qtable_cong[OF qtable_\<epsilon>_lax] split: if_splits)+
next
  case (Star r)
  then show ?case
    by (cases mr) (auto simp: qtable_unit_table split: if_splits)
qed

lemma rtranclp_False: "(\<lambda>i j. False)\<^sup>*\<^sup>* = (=)"
proof -
  have "(\<lambda>i j. False)\<^sup>*\<^sup>* i j \<Longrightarrow> i = j" for i j :: 'a
    by (induct i j rule: rtranclp.induct) auto
  then show ?thesis
    by (auto intro: exI[of _ 0])
qed

inductive ok_rctxt for \<phi>s where
  "ok_rctxt \<phi>s id id"
| "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> ok_rctxt \<phi>s (\<lambda>t. \<kappa> (MTimes mr t)) (\<lambda>t. \<kappa>' (Regex.Times (from_mregex mr \<phi>s) t))"

lemma ok_rctxt_swap: "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> from_mregex (\<kappa> mr) \<phi>s = \<kappa>' (from_mregex mr \<phi>s)"
  by (induct \<kappa> \<kappa>' arbitrary: mr rule: ok_rctxt.induct) auto

lemma ok_rctxt_cong: "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat \<sigma> V v) s \<Longrightarrow>
  Regex.match (Formula.sat \<sigma> V v) (\<kappa>' r) i j = Regex.match (Formula.sat \<sigma> V v) (\<kappa>' s) i j"
  by (induct \<kappa> \<kappa>' arbitrary: r s rule: ok_rctxt.induct) simp_all

lemma qtable_r\<delta>\<kappa>:
  assumes "ok (length \<phi>s) mr" "fv_regex (from_mregex mr \<phi>s) \<subseteq> A"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j \<phi>) rel) \<phi>s rels"
    and "ok_rctxt \<phi>s \<kappa> \<kappa>'"
    and "\<forall>ms \<in> \<kappa> ` RPD mr. qtable n A (mem_restr R) (\<lambda>v. Q (map the v) (from_mregex ms \<phi>s)) (lookup rel ms)"
  shows "qtable n A (mem_restr R)
  (\<lambda>v. \<exists>s \<in> Regex.rpd\<kappa> \<kappa>' (Formula.sat \<sigma> V (map the v)) j (from_mregex mr \<phi>s). Q (map the v) s)
  (r\<delta> \<kappa> rel rels mr)"
  using assms
proof (induct mr arbitrary: \<kappa> \<kappa>')
  case MSkip
  then show ?case
    by (auto simp: rtranclp_False ok_rctxt_swap qtable_empty_iff
        elim!: qtable_cong[OF _ _ ok_rctxt_cong[of _ \<kappa> \<kappa>']] split: nat.splits)
next
  case (MPlus mr1 mr2)
  from MPlus(3-7) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  from MTimes(3-7) show ?case
    by (auto intro!: qtable_union[OF MTimes(2) qtable_\<epsilon>_lax[OF _ _ _ MTimes(1)]]
        elim!: ok_rctxt.intros(2) simp: MTimesL_def Ball_def)
next
  case (MStar mr)
  from MStar(2-6) show ?case
    by (auto intro!: qtable_cong[OF MStar(1)] intro: ok_rctxt.intros simp: MTimesL_def Ball_def)
qed (auto simp: qtable_empty_iff)

lemmas qtable_r\<delta> = qtable_r\<delta>\<kappa>[OF _ _ _ ok_rctxt.intros(1), unfolded rpd\<kappa>_rpd image_id id_apply]

inductive ok_lctxt for \<phi>s where
  "ok_lctxt \<phi>s id id"
| "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> ok_lctxt \<phi>s (\<lambda>t. \<kappa> (MTimes t mr)) (\<lambda>t. \<kappa>' (Regex.Times t (from_mregex mr \<phi>s)))"

lemma ok_lctxt_swap: "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> from_mregex (\<kappa> mr) \<phi>s = \<kappa>' (from_mregex mr \<phi>s)"
  by (induct \<kappa> \<kappa>' arbitrary: mr rule: ok_lctxt.induct) auto

lemma ok_lctxt_cong: "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat \<sigma> V v) s \<Longrightarrow>
  Regex.match (Formula.sat \<sigma> V v) (\<kappa>' r) i j = Regex.match (Formula.sat \<sigma> V v) (\<kappa>' s) i j"
  by (induct \<kappa> \<kappa>' arbitrary: r s rule: ok_lctxt.induct) simp_all

lemma qtable_l\<delta>\<kappa>:
  assumes "ok (length \<phi>s) mr" "fv_regex (from_mregex mr \<phi>s) \<subseteq> A"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j \<phi>) rel) \<phi>s rels"
    and "ok_lctxt \<phi>s \<kappa> \<kappa>'"
    and "\<forall>ms \<in> \<kappa> ` LPD mr. qtable n A (mem_restr R) (\<lambda>v. Q (map the v) (from_mregex ms \<phi>s)) (lookup rel ms)"
  shows "qtable n A (mem_restr R)
  (\<lambda>v. \<exists>s \<in> Regex.lpd\<kappa> \<kappa>' (Formula.sat \<sigma> V (map the v)) j (from_mregex mr \<phi>s). Q (map the v) s)
  (l\<delta> \<kappa> rel rels mr)"
  using assms
proof (induct mr arbitrary: \<kappa> \<kappa>')
  case MSkip
  then show ?case
    by (auto simp: rtranclp_False ok_lctxt_swap qtable_empty_iff
        elim!: qtable_cong[OF _ _ ok_rctxt_cong[of _ \<kappa> \<kappa>']] split: nat.splits)
next
  case (MPlus mr1 mr2)
  from MPlus(3-7) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  from MTimes(3-7) show ?case
    by (auto intro!: qtable_union[OF MTimes(1) qtable_\<epsilon>_lax[OF _ _ _ MTimes(2)]]
        elim!: ok_lctxt.intros(2) simp: MTimesR_def Ball_def)
next
  case (MStar mr)
  from MStar(2-6) show ?case
    by (auto intro!: qtable_cong[OF MStar(1)] intro: ok_lctxt.intros simp: MTimesR_def Ball_def)
qed (auto simp: qtable_empty_iff)

lemmas qtable_l\<delta> = qtable_l\<delta>\<kappa>[OF _ _ _ ok_lctxt.intros(1), unfolded lpd\<kappa>_lpd image_id id_apply]

lemma RPD_fv_regex_le:
  "ms \<in> RPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) \<subseteq> fv_regex (from_mregex mr \<phi>s)"
  by (induct mr arbitrary: ms) (auto simp: MTimesL_def split: nat.splits)+

lemma RPD_safe: "safe_regex Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPD mr \<Longrightarrow> safe_regex Past g (from_mregex ms \<phi>s)"
proof (induct Past g "from_mregex mr \<phi>s" arbitrary: mr ms rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test g \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MPlus mr ms)
    with Plus(3-5) show ?thesis
      by (auto dest!: Plus(1,2))
  qed auto
next
  case (TimesP g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MTimes mr ms)
    with TimesP(3-5) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesL_def dest: RPD_fv_regex_le TimesP(1,2))
  qed auto
next
  case (Star g r)
  then show ?case
  proof (cases mr)
    case (MStar x6)
    with Star(2-4) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesL_def dest: RPD_fv_regex_le
          elim!: safe_cosafe[rotated] dest!: Star(1))
  qed auto
qed

lemma RPDi_safe: "safe_regex Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDi n mr ==> safe_regex Past g (from_mregex ms \<phi>s)"
  by (induct n arbitrary: ms mr) (auto dest: RPD_safe)

lemma RPDs_safe: "safe_regex Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDs mr ==> safe_regex Past g (from_mregex ms \<phi>s)"
  unfolding RPDs_def by (auto dest: RPDi_safe)

lemma RPD_safe_fv_regex: "safe_regex Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
proof (induct Past Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case (Skip n)
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus r s)
  then show ?case
    by (cases mr) auto
next
  case (TimesP r s)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesL_def dest: RPD_fv_regex_le split: modality.splits)
next
  case (Star r)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesL_def dest: RPD_fv_regex_le)
qed

lemma RPDi_safe_fv_regex: "safe_regex Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDi n mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  by (induct n arbitrary: ms mr) (auto 5 0 dest: RPD_safe_fv_regex RPD_safe)

lemma RPDs_safe_fv_regex: "safe_regex Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDs mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  unfolding RPDs_def by (auto dest: RPDi_safe_fv_regex)

lemma RPD_ok: "ok m mr \<Longrightarrow> ms \<in> RPD mr \<Longrightarrow> ok m ms"
proof (induct mr arbitrary: ms)
  case (MPlus mr1 mr2)
  from MPlus(3,4) show ?case
    by (auto elim: MPlus(1,2))
next
  case (MTimes mr1 mr2)
  from MTimes(3,4) show ?case
    by (auto elim: MTimes(1,2) simp: MTimesL_def)
next
  case (MStar mr)
  from MStar(2,3) show ?case
    by (auto elim: MStar(1) simp: MTimesL_def)
qed (auto split: nat.splits)

lemma RPDi_ok: "ok m mr \<Longrightarrow> ms \<in> RPDi n mr \<Longrightarrow> ok m ms"
  by (induct n arbitrary: ms mr) (auto intro: RPD_ok)

lemma RPDs_ok: "ok m mr \<Longrightarrow> ms \<in> RPDs mr \<Longrightarrow> ok m ms"
  unfolding RPDs_def by (auto intro: RPDi_ok)

lemma LPD_fv_regex_le:
  "ms \<in> LPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) \<subseteq> fv_regex (from_mregex mr \<phi>s)"
  by (induct mr arbitrary: ms) (auto simp: MTimesR_def split: nat.splits)+

lemma LPD_safe: "safe_regex Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPD mr ==> safe_regex Futu g (from_mregex ms \<phi>s)"
proof (induct Futu g "from_mregex mr \<phi>s" arbitrary: mr ms rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test g \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MPlus mr ms)
    with Plus(3-5) show ?thesis
      by (auto dest!: Plus(1,2))
  qed auto
next
  case (TimesF g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MTimes mr ms)
    with TimesF(3-5) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesR_def dest: LPD_fv_regex_le split: modality.splits dest: TimesF(1,2))
  qed auto
next
  case (Star g r)
  then show ?case
  proof (cases mr)
    case (MStar x6)
    with Star(2-4) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesR_def dest: LPD_fv_regex_le
          elim!: safe_cosafe[rotated] dest!: Star(1))
  qed auto
qed

lemma LPDi_safe: "safe_regex Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDi n mr ==> safe_regex Futu g (from_mregex ms \<phi>s)"
  by (induct n arbitrary: ms mr) (auto dest: LPD_safe)

lemma LPDs_safe: "safe_regex Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDs mr ==> safe_regex Futu g (from_mregex ms \<phi>s)"
  unfolding LPDs_def by (auto dest: LPDi_safe)

lemma LPD_safe_fv_regex: "safe_regex Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPD mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
proof (induct Futu Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus r s)
  then show ?case
    by (cases mr) auto
next
  case (TimesF r s)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesR_def dest: LPD_fv_regex_le split: modality.splits)
next
  case (Star r)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesR_def dest: LPD_fv_regex_le)
qed

lemma LPDi_safe_fv_regex: "safe_regex Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDi n mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  by (induct n arbitrary: ms mr) (auto 5 0 dest: LPD_safe_fv_regex LPD_safe)

lemma LPDs_safe_fv_regex: "safe_regex Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDs mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  unfolding LPDs_def by (auto dest: LPDi_safe_fv_regex)

lemma LPD_ok: "ok m mr \<Longrightarrow> ms \<in> LPD mr \<Longrightarrow> ok m ms"
proof (induct mr arbitrary: ms)
  case (MPlus mr1 mr2)
  from MPlus(3,4) show ?case
    by (auto elim: MPlus(1,2))
next
  case (MTimes mr1 mr2)
  from MTimes(3,4) show ?case
    by (auto elim: MTimes(1,2) simp: MTimesR_def)
next
  case (MStar mr)
  from MStar(2,3) show ?case
    by (auto elim: MStar(1) simp: MTimesR_def)
qed (auto split: nat.splits)

lemma LPDi_ok: "ok m mr \<Longrightarrow> ms \<in> LPDi n mr \<Longrightarrow> ok m ms"
  by (induct n arbitrary: ms mr) (auto intro: LPD_ok)

lemma LPDs_ok: "ok m mr \<Longrightarrow> ms \<in> LPDs mr \<Longrightarrow> ok m ms"
  unfolding LPDs_def by (auto intro: LPDi_ok)

lemma update_matchP:
  assumes pre: "wf_matchP_aux \<sigma> V n R I r aux ne"
    and safe: "safe_regex Past Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (RPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne \<phi>) rel) \<phi>s rels"
    and result_eq: "(rel, aux') = update_matchP n I mr mrs rels (\<tau> \<sigma> ne) aux"
  shows "wf_matchP_aux \<sigma> V n R I r aux' (Suc ne)"
    and "qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Formula.MatchP I r)) rel"
proof -
  let ?wf_tuple = "\<lambda>v. wf_tuple n (Formula.fv_regex r) v"
  let ?update = "\<lambda>rel t. mrtabulate mrs (\<lambda>mr.
    r\<delta> id rel rels mr \<union> (if t = \<tau> \<sigma> ne then r\<epsilon>_strict n rels mr else {}))"
  note sat.simps[simp del]

  define aux0 where "aux0 = [(t, ?update rel t). (t, rel) \<leftarrow> aux, memR I (\<tau> \<sigma> ne - t)]"
  have sorted_aux0: "sorted_wrt (\<lambda>x y. fst x > fst y) aux0"
    using pre[unfolded wf_matchP_aux_def, THEN conjunct1]
    unfolding aux0_def
    by (induction aux) (auto simp add: sorted_wrt_append)
  { fix ms
    assume "ms \<in> RPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "safe_regex Past Strict (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "RPD ms \<subseteq> RPDs mr"
      using safe RPDs_safe RPDs_safe_fv_regex mr from_mregex_to_mregex RPDs_ok to_mregex_ok RPDs_trans
      by fastforce+
  } note * = this
  have **: "\<tau> \<sigma> ne - (\<tau> \<sigma> i + \<tau> \<sigma> ne - \<tau> \<sigma> (ne - Suc 0)) = \<tau> \<sigma> (ne - Suc 0) - \<tau> \<sigma> i" for i
    by (metis (no_types, lifting) Nat.diff_diff_right \<tau>_mono add.commute add_diff_cancel_left diff_le_self le_add2 order_trans)
  have ***: "\<tau> \<sigma> i = \<tau> \<sigma> ne"
    if  "\<tau> \<sigma> ne \<le> \<tau> \<sigma> i" "\<tau> \<sigma> i \<le> \<tau> \<sigma> (ne - Suc 0)" "ne > 0" for i
    by (metis (no_types, lifting) Suc_pred \<tau>_mono diff_le_self le_\<tau>_less le_antisym not_less_eq that)
  then have in_aux0_1: "(t, X) \<in> set aux0 \<Longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> ne \<and> memR I (\<tau> \<sigma> ne - t) \<and>
      (\<exists>i. \<tau> \<sigma> i = t) \<and>
      (\<forall>ms\<in>RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne
         (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms))" for t X
    unfolding aux0_def using safe mr mrs
    by (auto simp: lookup_tabulate map_of_map_restrict restrict_map_def finite_RPDs * ** RPDs_trans diff_le_mono2
        intro!: sat_MatchP_rec[of \<sigma> _ _ ne, THEN iffD2]
        qtable_union[OF qtable_r\<delta>[OF _ _ qtables] qtable_r\<epsilon>_strict[OF _ _ _ qtables],
          of ms "fv_regex r" "\<lambda>v r. Formula.sat \<sigma> V v (ne - Suc 0) (Formula.MatchP (point 0) r)" _ ms for ms]
        qtable_cong[OF qtable_r\<delta>[OF _ _ qtables],
          of ms "fv_regex r" "\<lambda>v r. Formula.sat \<sigma> V v (ne - Suc 0) (Formula.MatchP (point (\<tau> \<sigma> (ne - Suc 0) - \<tau> \<sigma> i)) r)"
          _ _  "(\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Formula.MatchP (point (\<tau> \<sigma> ne - \<tau> \<sigma> i))  (from_mregex ms \<phi>s)))" for ms i]
        dest!: assms(1)[unfolded wf_matchP_aux_def, THEN conjunct2, THEN conjunct1, rule_format]
        sat_MatchP_rec["of" \<sigma> _ _ ne, THEN iffD1]
        elim!: bspec order.trans[OF _ \<tau>_mono] bexI[rotated] split: option.splits if_splits) (* slow 7 sec *)
  then have in_aux0_le_\<tau>: "(t, X) \<in> set aux0 \<Longrightarrow> t \<le> \<tau> \<sigma> ne" for t X
    by (meson \<tau>_mono diff_le_self le_trans)
  have in_aux0_2: "ne \<noteq> 0 \<Longrightarrow> t \<le> \<tau> \<sigma> (ne-1) \<Longrightarrow> memR I (\<tau> \<sigma> ne - t) \<Longrightarrow> \<exists>i. \<tau> \<sigma> i = t \<Longrightarrow>
    \<exists>X. (t, X) \<in> set aux0" for t
  proof -
    fix t
    assume "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne-1)" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t"
    then obtain X where "(t, X) \<in> set aux"
      by (atomize_elim, intro assms(1)[unfolded wf_matchP_aux_def, THEN conjunct2, THEN conjunct2, rule_format])
        (auto simp: gr0_conv_Suc elim!: order_trans[rotated] intro!: diff_le_mono \<tau>_mono)
    with \<open>memR I (\<tau> \<sigma> ne - t)\<close> have "(t, ?update X t) \<in> set aux0"
      unfolding aux0_def by (auto simp: id_def elim!: bexI[rotated] intro!: exI[of _ X])
    then show "\<exists>X. (t, X) \<in> set aux0"
      by blast
  qed
  have aux0_Nil: "aux0 = [] \<Longrightarrow> ne = 0 \<or> ne \<noteq> 0 \<and> (\<forall>t. t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> ne - t) \<longrightarrow>
        (\<nexists>i. \<tau> \<sigma> i = t))"
    using in_aux0_2 by (cases "ne = 0") (auto)

  have aux'_eq: "aux' = (case aux0 of
      [] \<Rightarrow> [(\<tau> \<sigma> ne, mrtabulate mrs (r\<epsilon>_strict n rels))]
    | x # aux' \<Rightarrow> (if fst x = \<tau> \<sigma> ne then x # aux'
       else (\<tau> \<sigma> ne, mrtabulate mrs (r\<epsilon>_strict n rels)) # x # aux'))"
    using result_eq unfolding aux0_def update_matchP_def Let_def by simp
  have sorted_aux': "sorted_wrt (\<lambda>x y. fst x > fst y) aux'"
    unfolding aux'_eq
    using sorted_aux0 in_aux0_le_\<tau> by (cases aux0) (fastforce)+

  have in_aux'_1: "t \<le> \<tau> \<sigma> ne \<and> memR I (\<tau> \<sigma> ne - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
     (\<forall>ms\<in>RPDs mr. qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v.
        Formula.sat \<sigma> V (map the v) ne (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms))"
    if aux': "(t, X) \<in> set aux'" for t X
  proof (cases aux0)
    case Nil
    with aux' show ?thesis
      unfolding aux'_eq using safe mrs qtables aux0_Nil *
      by (auto simp: zero_enat_def[symmetric] sat_MatchP_rec[where i=ne]
          lookup_tabulate finite_RPDs split: option.splits
          intro!: qtable_cong[OF qtable_r\<epsilon>_strict]
          dest: spec[of _ "\<tau> \<sigma> (ne-1)"])
  next
    case (Cons a as)
    show ?thesis
    proof (cases "t = \<tau> \<sigma> ne")
      case t: True
      show ?thesis
      proof (cases "fst a = \<tau> \<sigma> ne")
        case True
        with aux' Cons t have "X = snd a"
          unfolding aux'_eq using sorted_aux0 by auto
        moreover from in_aux0_1[of "fst a" "snd a"] Cons have "ne \<noteq> 0"
          "fst a \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - fst a)" "\<exists>i. \<tau> \<sigma> i = fst a"
          "\<forall>ms \<in> RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne
            (Formula.MatchP (point (\<tau> \<sigma> ne - fst a)) (from_mregex ms \<phi>s))) (lookup (snd a) ms)"
          by auto
        ultimately show ?thesis using t True
          by auto
      next
        case False
        with aux' Cons t have "X = mrtabulate mrs (r\<epsilon>_strict n rels)"
          unfolding aux'_eq using sorted_aux0 in_aux0_le_\<tau>[of "fst a" "snd a"] by auto
        with aux' Cons t False show ?thesis
          unfolding aux'_eq using safe mrs qtables * in_aux0_2[of "\<tau> \<sigma> (ne-1)"] in_aux0_le_\<tau>[of "fst a" "snd a"] sorted_aux0
          by (auto simp: sat_MatchP_rec[where i=ne] zero_enat_def[symmetric] enat_0_iff not_le
              lookup_tabulate finite_RPDs split: option.splits
              intro!: qtable_cong[OF qtable_r\<epsilon>_strict] dest!: le_\<tau>_less meta_mp)
      qed
    next
      case False
      with aux' Cons have "(t, X) \<in> set aux0"
        unfolding aux'_eq by (auto split: if_splits)
      then have "ne \<noteq> 0" "t \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t"
        "\<forall>ms \<in> RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne
          (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms)"
        using in_aux0_1 by blast+
      with False aux' Cons show ?thesis
        unfolding aux'_eq by auto
    qed
  qed

  have in_aux'_2: "\<exists>X. (t, X) \<in> set aux'" if "t \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t" for t
  proof (cases "t = \<tau> \<sigma> ne")
    case True
    then show ?thesis
    proof (cases aux0)
      case Nil
      with True show ?thesis unfolding aux'_eq by simp
    next
      case (Cons a as)
      with True show ?thesis unfolding aux'_eq using eq_fst_iff[of t a]
        by (cases "fst a = \<tau> \<sigma> ne") auto
    qed
  next
    case False
    with that have "ne \<noteq> 0"
      using le_\<tau>_less neq0_conv by blast
    moreover from False that have  "t \<le> \<tau> \<sigma> (ne-1)"
      by (metis One_nat_def Suc_leI Suc_pred \<tau>_mono diff_is_0_eq' order.antisym neq0_conv not_le)
    ultimately obtain X where "(t, X) \<in> set aux0" using \<open>memR I (\<tau> \<sigma> ne - t)\<close> \<open>\<exists>i. \<tau> \<sigma> i = t\<close>
      by atomize_elim (auto intro!: in_aux0_2)
    then show ?thesis unfolding aux'_eq using False
      by (auto intro: exI[of _ X] split: list.split)
  qed

  show "wf_matchP_aux \<sigma> V n R I r aux' (Suc ne)"
    unfolding wf_matchP_aux_def using mr
    by (auto dest: in_aux'_1 intro: sorted_aux' in_aux'_2)

  have rel_eq: "rel = foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux', memL I (\<tau> \<sigma> ne - t)] {}"
    unfolding aux'_eq aux0_def
    using result_eq by (simp add: update_matchP_def Let_def)
  have rel_alt: "rel = (\<Union>(t, rel) \<in> set aux'. if memL I (\<tau> \<sigma> ne - t) then lookup rel mr else empty_table)"
    unfolding rel_eq
    by (auto elim!: in_foldr_UnE bexI[rotated] intro!: in_foldr_UnI)
  show "qtable n (fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Formula.MatchP I r)) rel"
    unfolding rel_alt
  proof (rule qtable_Union[where Qi="\<lambda>(t, X) v.
    memL I (\<tau> \<sigma> ne - t) \<and> Formula.sat \<sigma> V (map the v) ne (Formula.MatchP (point (\<tau> \<sigma> ne - t)) r)"],
        goal_cases finite qtable equiv)
    case (equiv v)
    show ?case
    proof (rule iffI, erule sat_MatchP_point, goal_cases left right)
      case (left j)
      then show ?case using in_aux'_2[of "\<tau> \<sigma> j", OF _ _ exI, OF _ _ refl] by auto
    next
      case right
      then show ?case by (auto elim!: sat_MatchP_pointD dest: in_aux'_1)
    qed
  qed (auto dest!: in_aux'_1 intro!: qtable_empty dest!: bspec[OF _ RPDs_refl]
      simp: from_mregex_eq[OF safe mr])
qed

lemma length_update_until: "length (update_until args rel1 rel2 nt aux) = Suc (length aux)"
  unfolding update_until_def by simp

lemma wf_update_until_auxlist:
  assumes pre: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne"
    and qtable1: "qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length auxlist) \<phi>) rel1"
    and qtable2: "qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length auxlist) \<psi>) rel2"
    and fvi_subset: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_pos: "args_pos args = pos"
  shows "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> (update_until args rel1 rel2 (\<tau> \<sigma> (ne + length auxlist)) auxlist) ne"
  unfolding wf_until_auxlist_def length_update_until
  unfolding update_until_def list.rel_map add_Suc_right upt.simps eqTrueI[OF le_add1] if_True
proof (rule list_all2_appendI, unfold list.rel_map, goal_cases old new)
  case old
  show ?case
  proof (rule list.rel_mono_strong[OF assms(1)[unfolded wf_until_auxlist_def]]; safe, goal_cases mono1 mono2)
    case (mono1 i X Y v)
    then show ?case
      by (fastforce simp: args_ivl args_n args_pos sat_the_restrict less_Suc_eq
          elim!: qtable_join[OF _ qtable1] qtable_union[OF _ qtable1])
  next
    case (mono2 i X Y v)
    then show ?case using fvi_subset
      by (auto 0 3 simp: args_ivl args_n args_pos sat_the_restrict less_Suc_eq split: if_splits
          elim!: qtable_union[OF _ qtable_join_fixed[OF qtable2]]
          elim: qtable_cong[OF _ refl] intro: exI[of _ "ne + length auxlist"]) (* slow 8 sec*)
  qed
next
  case new
  then show ?case
    by (auto intro!: qtable_empty qtable1 qtable2[THEN qtable_cong] exI[of _ "ne + length auxlist"]
        simp: args_ivl args_n args_pos less_Suc_eq zero_enat_def[symmetric])
qed

lemma (in muaux) wf_update_until:
  assumes pre: "wf_until_aux \<sigma> V R args \<phi> \<psi> aux ne"
    and qtable1: "qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length_muaux args aux) \<phi>) rel1"
    and qtable2: "qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length_muaux args aux) \<psi>) rel2"
    and fvi_subset: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>"
    and args_R: "args_R args = Formula.fv \<psi>"
    and args_pos: "args_pos args = pos"
  shows "wf_until_aux \<sigma> V R args \<phi> \<psi> (add_new_muaux args rel1 rel2 (\<tau> \<sigma> (ne + length_muaux args aux)) aux) ne \<and>
      length_muaux args (add_new_muaux args rel1 rel2 (\<tau> \<sigma> (ne + length_muaux args aux)) aux) = Suc (length_muaux args aux)"
proof -
  from pre obtain cur auxlist where valid_aux: "valid_muaux args cur aux auxlist" and
    cur: "cur = (if ne + length auxlist = 0 then 0 else \<tau> \<sigma> (ne + length auxlist - 1))" and
    pre_list: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne"
    unfolding wf_until_aux_def args_ivl args_n args_pos by auto
  have length_aux: "length_muaux args aux = length auxlist"
    using valid_length_muaux[OF valid_aux] .
  define nt where "nt \<equiv> \<tau> \<sigma> (ne + length_muaux args aux)"
  have nt_mono: "cur \<le> nt"
    unfolding cur nt_def length_aux by simp
  define auxlist' where "auxlist' \<equiv> update_until args rel1 rel2 (\<tau> \<sigma> (ne + length auxlist)) auxlist"
  have length_auxlist': "length auxlist' = Suc (length auxlist)"
    unfolding auxlist'_def by (auto simp add: length_update_until)
  have tab1: "table (args_n args) (args_L args) rel1"
    using qtable1 unfolding args_n[symmetric] args_L[symmetric] by (auto simp add: qtable_def)
  have tab2: "table (args_n args) (args_R args) rel2"
    using qtable2 unfolding args_n[symmetric] args_R[symmetric] by (auto simp add: qtable_def)
  have fv_sub: "fv \<phi> \<subseteq> fv \<psi>"
    using pre unfolding wf_until_aux_def by auto
  moreover have valid_add_new_auxlist: "valid_muaux args nt (add_new_muaux args rel1 rel2 nt aux) auxlist'"
    using valid_add_new_muaux[OF valid_aux tab1 tab2 nt_mono]
    unfolding auxlist'_def nt_def length_aux .
  moreover have "length_muaux args (add_new_muaux args rel1 rel2 nt aux) = Suc (length_muaux args aux)"
    using valid_length_muaux[OF valid_add_new_auxlist] unfolding length_auxlist' length_aux[symmetric] .
  moreover have "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist' ne"
    using wf_update_until_auxlist[OF pre_list qtable1[unfolded length_aux] qtable2[unfolded length_aux] fv_sub args_ivl args_n args_pos]
    unfolding auxlist'_def .
  moreover have "\<tau> \<sigma> (ne + length auxlist) = (if ne + length auxlist' = 0 then 0 else \<tau> \<sigma> (ne + length auxlist' - 1))"
    unfolding cur length_auxlist' by auto
  ultimately show ?thesis
    unfolding wf_until_aux_def nt_def length_aux args_ivl args_n args_pos by fast
qed

lemma length_update_matchF_base:
  "length (fst (update_matchF_base I mr mrs nt entry st)) = Suc 0"
  by (auto simp: Let_def update_matchF_base_def)

lemma length_update_matchF_step:
  "length (fst (update_matchF_step I mr mrs nt entry st)) = Suc (length (fst st))"
  by (auto simp: Let_def update_matchF_step_def split: prod.splits)

lemma length_foldr_update_matchF_step:
  "length (fst (foldr (update_matchF_step I mr mrs nt) aux base)) = length aux + length (fst base)"
  by (induct aux arbitrary: base) (auto simp: Let_def length_update_matchF_step)

lemma length_update_matchF: "length (update_matchF n I mr mrs rels nt aux) = Suc (length aux)"
  unfolding update_matchF_def update_matchF_base_def length_foldr_update_matchF_step
  by (auto simp: Let_def)

lemma wf_update_matchF_base_invar:
  assumes safe: "safe_regex Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j \<phi>) rel) \<phi>s rels"
  shows "wf_matchF_invar \<sigma> V n R I r (update_matchF_base n I mr mrs rels (\<tau> \<sigma> j)) j"
proof -
  have from_mregex: "from_mregex mr \<phi>s = r"
    using safe mr using from_mregex_eq by blast
  { fix ms
    assume "ms \<in> LPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "safe_regex Futu Strict (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "LPD ms \<subseteq> LPDs mr"
      using safe LPDs_safe LPDs_safe_fv_regex mr from_mregex_to_mregex LPDs_ok to_mregex_ok LPDs_trans
      by fastforce+
  } note * = this
  show ?thesis
    unfolding wf_matchF_invar_def wf_matchF_aux_def update_matchF_base_def mr prod.case Let_def mrs
    using safe
    by (auto simp: * from_mregex qtables qtable_empty_iff zero_enat_def[symmetric]
        lookup_tabulate finite_LPDs eps_match less_Suc_eq LPDs_refl
        intro!: qtable_cong[OF qtable_l\<epsilon>_strict[where \<phi>s=\<phi>s]] intro: qtables exI[of _ j]
        split: option.splits)
qed

lemma Un_empty_table[simp]: "rel \<union> empty_table = rel" "empty_table \<union> rel = rel"
  unfolding empty_table_def by auto

lemma wf_matchF_invar_step:
  assumes wf: "wf_matchF_invar \<sigma> V n R I r st (Suc i)"
    and safe: "safe_regex Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel) \<phi>s rels"
    and rel: "qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < i + length (fst st) \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and>
          Regex.match (Formula.sat \<sigma> V (map the v)) r i j)) rel"
    and entry: "entry = (\<tau> \<sigma> i, rels, rel)"
    and nt: "nt = \<tau> \<sigma> (i + length (fst st))"
  shows "wf_matchF_invar \<sigma> V n R I r (update_matchF_step I mr mrs nt entry st) i"
proof -
  have from_mregex: "from_mregex mr \<phi>s = r"
    using safe mr using from_mregex_eq by blast
  { fix ms
    assume "ms \<in> LPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "safe_regex Futu Strict (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "LPD ms \<subseteq> LPDs mr"
      using safe LPDs_safe LPDs_safe_fv_regex mr from_mregex_to_mregex LPDs_ok to_mregex_ok LPDs_trans
      by fastforce+
  } note * = this
  { fix aux X ms
    assume "st = (aux, X)" "ms \<in> LPDs mr"
    with wf mr have "qtable n (fv_regex r) (mem_restr R)
      (\<lambda>v. Regex.match (Formula.sat \<sigma> V (map the v)) (from_mregex ms \<phi>s) i (i + length aux))
      (l\<delta> (\<lambda>x. x) X rels ms)"
      by (intro qtable_cong[OF qtable_l\<delta>[where \<phi>s=\<phi>s and A="fv_regex r" and
              Q="\<lambda>v r. Regex.match (Formula.sat \<sigma> V v) r (Suc i) (i + length aux)", OF _ _ qtables]])
        (auto simp: wf_matchF_invar_def * LPDs_trans lpd_match[of i] elim!: bspec)
  } note l\<delta> = this
  have "lookup (mrtabulate mrs f) ms = f ms" if "ms \<in> LPDs mr" for ms and f :: "mregex \<Rightarrow> 'a table"
    using that mrs  by (fastforce simp: lookup_tabulate finite_LPDs split: option.splits)+
  then show ?thesis
    using wf mr mrs entry nt LPDs_trans
    by (auto 0 3 simp: Let_def wf_matchF_invar_def update_matchF_step_def wf_matchF_aux_def mr * LPDs_refl
        list_all2_Cons1 append_eq_Cons_conv upt_eq_Cons_conv Suc_le_eq qtables
        lookup_tabulate finite_LPDs id_def l\<delta> from_mregex less_Suc_eq
        intro!: qtable_union[OF rel l\<delta>] qtable_cong[OF rel]
        intro: exI[of _ "i + length _"]
        split: if_splits prod.splits)
qed

lemma wf_update_matchF_invar:
  assumes pre: "wf_matchF_aux \<sigma> V n R I r aux ne (length (fst st) - 1)"
    and wf: "wf_matchF_invar \<sigma> V n R I r st (ne + length aux)"
    and safe: "safe_regex Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and j: "j = ne + length aux + length (fst st) - 1"
  shows "wf_matchF_invar \<sigma> V n R I r (foldr (update_matchF_step I mr mrs (\<tau> \<sigma> j)) aux st) ne"
  using pre wf unfolding j
proof (induct aux arbitrary: ne)
  case (Cons entry aux)
  from Cons(1)[of "Suc ne"] Cons(2,3) show ?case
    unfolding foldr.simps o_apply
    by (intro wf_matchF_invar_step[where rels = "fst (snd entry)" and rel = "snd (snd entry)"])
      (auto simp: safe mr mrs wf_matchF_aux_def wf_matchF_invar_def list_all2_Cons1 append_eq_Cons_conv
        Suc_le_eq upt_eq_Cons_conv length_foldr_update_matchF_step add.assoc split: if_splits)
qed simp


lemma wf_update_matchF:
  assumes pre: "wf_matchF_aux \<sigma> V n R I r aux ne 0"
    and safe: "safe_regex Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and nt: "nt = \<tau> \<sigma> (ne + length aux)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length aux) \<phi>) rel) \<phi>s rels"
  shows "wf_matchF_aux \<sigma> V n R I r (update_matchF n I mr mrs rels nt aux) ne 0"
  unfolding update_matchF_def using wf_update_matchF_base_invar[OF safe mr mrs qtables, of I]
  unfolding nt
  by (intro wf_update_matchF_invar[OF _ _ safe mr mrs, unfolded wf_matchF_invar_def split_beta, THEN conjunct2, THEN conjunct1])
    (auto simp: length_update_matchF_base wf_matchF_invar_def update_matchF_base_def Let_def pre)

lemma wf_until_aux_Cons: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> (a # aux) ne \<Longrightarrow>
  wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> aux (Suc ne)"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong)

lemma wf_matchF_aux_Cons: "wf_matchF_aux \<sigma> V n R I r (entry # aux) ne i \<Longrightarrow>
  wf_matchF_aux \<sigma> V n R I r aux (Suc ne) i"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong split: prod.splits)

lemma wf_until_aux_Cons1: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma wf_matchF_aux_Cons1: "wf_matchF_aux \<sigma> V n R I r ((t, rels, rel) # aux) ne i \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc split: prod.splits)

lemma wf_until_aux_Cons3: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow>
  qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux) \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> ne)) \<and>
    Formula.sat \<sigma> V (map the v) j \<psi> \<and> (\<forall>k\<in>{ne..<j}. if pos then Formula.sat \<sigma> V (map the v) k \<phi> else \<not> Formula.sat \<sigma> V (map the v) k \<phi>))) a2"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma wf_matchF_aux_Cons3: "wf_matchF_aux \<sigma> V n R I r ((t, rels, rel) # aux) ne i \<Longrightarrow>
  qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux + i) \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> ne)) \<and>
    Regex.match (Formula.sat \<sigma> V (map the v)) r ne j)) rel"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc split: prod.splits)

lemma upt_append: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<b] @ [b..<c] = [a..<c]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma wf_mbuf2_add:
  assumes "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 P [ja..<ja'] xs"
    and "list_all2 Q [jb..<jb'] ys"
    and "ja \<le> ja'" "jb \<le> jb'"
  shows "wf_mbuf2 i ja' jb' P Q (mbuf2_add xs ys buf)"
  using assms unfolding wf_mbuf2_def
  by (auto 0 3 simp: list_all2_append2 upt_append dest: list_all2_lengthD
      intro: exI[where x="[i..<ja]"] exI[where x="[ja..<ja']"]
      exI[where x="[i..<jb]"] exI[where x="[jb..<jb']"] split: prod.splits)

lemma wf_mbufn_add:
  assumes "wf_mbufn i js Ps buf"
    and "list_all3 list_all2 Ps (List.map2 (\<lambda>j j'. [j..<j']) js js') xss"
    and "list_all2 (\<le>) js js'"
  shows "wf_mbufn i js' Ps (mbufn_add xss buf)"
  unfolding wf_mbufn_def list_all3_conv_all_nth
proof safe
  show "length Ps = length js'" "length js' = length (mbufn_add xss buf)"
    using assms unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth by auto
next
  fix k assume k: "k < length Ps"
  then show "i \<le> js' ! k"
    using assms unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth
    by (auto 0 4 dest: spec[of _ i])
  from k have " [i..<js' ! k] =  [i..<js ! k] @ [js ! k ..<js' ! k]" and
    "length [i..<js ! k] = length (buf ! k)"
    using assms(1,3) unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth
    by (auto simp: upt_append)
  with k show "list_all2 (Ps ! k) [i..<js' ! k] (mbufn_add xss buf ! k)"
    using assms[unfolded wf_mbufn_def list_all3_conv_all_nth]
    by (auto simp add: list_all2_append)
qed

lemma mbuf2_take_eqD:
  assumes "mbuf2_take f buf = (xs, buf')"
    and "wf_mbuf2 i ja jb P Q buf"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 (\<lambda>i z. \<exists>x y. P i x \<and> Q i y \<and> z = f x y) [i..<min ja jb] xs"
  using assms unfolding wf_mbuf2_def
  by (induction f buf arbitrary: i xs buf' rule: mbuf2_take.induct)
    (fastforce simp add: list_all2_Cons2 upt_eq_Cons_conv min_absorb1 min_absorb2 split: prod.splits)+

lemma list_all3_Nil[simp]:
  "list_all3 P xs ys [] \<longleftrightarrow> xs = [] \<and> ys = []"
  "list_all3 P xs [] zs \<longleftrightarrow> xs = [] \<and> zs = []"
  "list_all3 P [] ys zs \<longleftrightarrow> ys = [] \<and> zs = []"
  unfolding list_all3_conv_all_nth by auto

lemma list_all3_Cons:
  "list_all3 P xs ys (z # zs) \<longleftrightarrow> (\<exists>x xs' y ys'. xs = x # xs' \<and> ys = y # ys' \<and> P x y z \<and> list_all3 P xs' ys' zs)"
  "list_all3 P xs (y # ys) zs \<longleftrightarrow> (\<exists>x xs' z zs'. xs = x # xs' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs' ys zs')"
  "list_all3 P (x # xs) ys zs \<longleftrightarrow> (\<exists>y ys' z zs'. ys = y # ys' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs ys' zs')"
  unfolding list_all3_conv_all_nth
  by (auto simp: length_Suc_conv Suc_length_conv nth_Cons split: nat.splits)

lemma list_all3_mono_strong: "list_all3 P xs ys zs \<Longrightarrow>
  (\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> P x y z \<Longrightarrow> Q x y z) \<Longrightarrow>
  list_all3 Q xs ys zs"
  by (induct xs ys zs rule: list_all3.induct) (auto intro: list_all3.intros)

definition Mini where
  "Mini i js = (if js = [] then i else Min (set js))"

lemma wf_mbufn_in_set_Mini:
  assumes "wf_mbufn i js Ps buf"
  shows "[] \<in> set buf \<Longrightarrow> Mini i js = i"
  unfolding in_set_conv_nth
proof (elim exE conjE)
  fix k
  have "i \<le> j" if "j \<in> set js" for j
    using that assms unfolding wf_mbufn_def list_all3_conv_all_nth in_set_conv_nth by auto
  moreover assume "k < length buf" "buf ! k = []"
  ultimately show ?thesis using assms
    unfolding Mini_def wf_mbufn_def list_all3_conv_all_nth
    by (auto 0 4 dest!: spec[of _ k] intro: Min_eqI simp: in_set_conv_nth)
qed

lemma wf_mbufn_notin_set:
  assumes "wf_mbufn i js Ps buf"
  shows "[] \<notin> set buf \<Longrightarrow> j \<in> set js \<Longrightarrow> i < j"
  using assms unfolding wf_mbufn_def list_all3_conv_all_nth
  by (cases "i \<in> set js") (auto intro: le_neq_implies_less simp: in_set_conv_nth)

lemma wf_mbufn_map_tl:
  "wf_mbufn i js Ps buf \<Longrightarrow> [] \<notin> set buf \<Longrightarrow> wf_mbufn (Suc i) js Ps (map tl buf)"
  by (auto simp: wf_mbufn_def list_all3_map Suc_le_eq
      dest: rel_funD[OF tl_transfer]  elim!: list_all3_mono_strong le_neq_implies_less)

lemma list_all3_list_all2I: "list_all3 (\<lambda>x y z. Q x z) xs ys zs \<Longrightarrow> list_all2 Q xs zs"
  by (induct xs ys zs rule: list_all3.induct) auto

lemma mbuf2t_take_eqD:
  assumes "mbuf2t_take f z buf nts = (z', buf', nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 R [min ja jb..<j] nts'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf nts arbitrary: i z' buf' nts' rule: mbuf2t_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      split: prod.split)

lemma wf_mbufn_take:
  assumes "mbufn_take f z buf = (z', buf')"
    and "wf_mbufn i js Ps buf"
  shows "wf_mbufn (Mini i js) js Ps buf'"
  using assms unfolding wf_mbufn_def
proof (induction f z buf arbitrary: i z' buf' rule: mbufn_take.induct)
  case rec: (1 f z buf)
  show ?case proof (cases "buf = []")
    case True
    with rec.prems show ?thesis by simp
  next
    case nonempty: False
    show ?thesis proof (cases "[] \<in> set buf")
      case True
      from rec.prems(2) have "\<forall>j\<in>set js. i \<le> j"
        by (auto simp: in_set_conv_nth list_all3_conv_all_nth)
      moreover from True rec.prems(2) have "i \<in> set js"
        by (fastforce simp: in_set_conv_nth list_all3_conv_all_nth list_all2_iff)
      ultimately have "Mini i js = i"
        unfolding Mini_def
        by (auto intro!: antisym[OF Min.coboundedI Min.boundedI])
      with rec.prems nonempty True show ?thesis by simp
    next
      case False
      from nonempty rec.prems(2) have "Mini i js = Mini (Suc i) js"
        unfolding Mini_def by auto
      show ?thesis
        unfolding \<open>Mini i js = Mini (Suc i) js\<close>
      proof (rule rec.IH)
        show "\<not> (buf = [] \<or> [] \<in> set buf)" using nonempty False by simp
        show "list_all3 (\<lambda>P j xs. Suc i \<le> j \<and> list_all2 P [Suc i..<j] xs) Ps js (map tl buf)"
          using False rec.prems(2)
          by (auto simp: list_all3_map elim!: list_all3_mono_strong dest: list.rel_sel[THEN iffD1])
        show "mbufn_take f (f (map hd buf) z) (map tl buf) = (z', buf')"
          using nonempty False rec.prems(1) by simp
      qed
    qed
  qed
qed

lemma mbufnt_take_eqD:
  assumes "mbufnt_take f z buf nts = (z', buf', nts')"
    and "wf_mbufn i js Ps buf"
    and "list_all2 R [i..<j] nts"
    and "\<And>k. k \<in> set js \<Longrightarrow> k \<le> j"
    and "k = Mini (i + length nts) js"
  shows "wf_mbufn k js Ps buf'"
    and "list_all2 R [k..<j] nts'"
  using assms(1-4) unfolding assms(5)
proof (induction f z buf nts arbitrary: i z' buf' nts' rule: mbufnt_take.induct)
  case IH: (1 f z buf nts)
  note mbufnt_take.simps[simp del]
  case 1
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  from 1 show ?case
    using wf_mbufn_in_set_Mini[OF 1(2)]
    by (subst (asm) mbufnt_take.simps)
      (force simp: Mini_def wf_mbufn_def split: if_splits prod.splits elim!: list_all3_mono_strong
        dest!: IH(1)[rotated, OF _ wf_mbufn_map_tl[OF 1(2)] *])
  case 2
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  have [simp]: "Suc (i + (length nts - Suc 0)) = i + length nts" if "nts \<noteq> []"
    using that by (fastforce simp flip: length_greater_0_conv)
  with 2 show ?case
    using wf_mbufn_in_set_Mini[OF 2(2)] wf_mbufn_notin_set[OF 2(2)]
    by (subst (asm) mbufnt_take.simps) (force simp: Mini_def wf_mbufn_def
        dest!: IH(2)[rotated, OF _ wf_mbufn_map_tl[OF 2(2)] *]
        split: if_splits prod.splits)
qed

lemma mbuf2t_take_induct[consumes 5, case_names base step]:
  assumes "mbuf2t_take f z buf nts = (z', buf', nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
    and "U i z"
    and "\<And>k x y t z. i \<le> k \<Longrightarrow> Suc k \<le> ja \<Longrightarrow> Suc k \<le> jb \<Longrightarrow>
      P k x \<Longrightarrow> Q k y \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f x y t z)"
  shows "U (min ja jb) z'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf nts arbitrary: i z' buf' nts' rule: mbuf2t_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated] split: prod.split)

lemma list_all2_hdD:
  assumes "list_all2 P [i..<j] xs" "xs \<noteq> []"
  shows "P i (hd xs)" "i < j"
  using assms unfolding list_all2_conv_all_nth
  by (auto simp: hd_conv_nth intro: zero_less_diff[THEN iffD1] dest!: spec[of _ 0])

lemma list_all2_lastD:
  assumes "list_all2 P [i..<j] xs" "xs \<noteq> []"
  shows "P (j - 1) (last xs)"
  using assms list_all2_hdD(2)[OF assms, THEN less_imp_add_positive] unfolding list_all2_conv_all_nth
  by (auto dest!: spec[of _ "length xs - 1"] simp: last_conv_nth Suc_le_eq)

lemma mbufn_take_induct[consumes 3, case_names base step]:
  assumes "mbufn_take f z buf = (z', buf')"
    and "wf_mbufn i js Ps buf"
    and "U i z"
    and "\<And>k xs z. i \<le> k \<Longrightarrow> Suc k \<le> Mini i js \<Longrightarrow>
      list_all2 (\<lambda>P x. P k x) Ps xs \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs z)"
  shows "U (Mini i js) z'"
  using assms unfolding wf_mbufn_def
proof (induction f z buf arbitrary: i z' buf' rule: mbufn_take.induct)
  case rec: (1 f z buf)
  show ?case proof (cases "buf = []")
    case True
    with rec.prems show ?thesis unfolding Mini_def by simp
  next
    case nonempty: False
    show ?thesis proof (cases "[] \<in> set buf")
      case True
      from rec.prems(2) have "\<forall>j\<in>set js. i \<le> j"
        by (auto simp: in_set_conv_nth list_all3_conv_all_nth)
      moreover from True rec.prems(2) have "i \<in> set js"
        by (fastforce simp: in_set_conv_nth list_all3_conv_all_nth list_all2_iff)
      ultimately have "Mini i js = i"
        unfolding Mini_def
        by (auto intro!: antisym[OF Min.coboundedI Min.boundedI])
      with rec.prems nonempty True show ?thesis by simp
    next
      case False
      with nonempty rec.prems(2) have more: "Suc i \<le> Mini i js"
        using diff_is_0_eq not_le unfolding Mini_def
        by (fastforce simp: in_set_conv_nth list_all3_conv_all_nth list_all2_iff)
      then have "Mini i js = Mini (Suc i) js" unfolding Mini_def by auto
      show ?thesis
        unfolding \<open>Mini i js = Mini (Suc i) js\<close>
      proof (rule rec.IH)
        show "\<not> (buf = [] \<or> [] \<in> set buf)" using nonempty False by simp
        show "mbufn_take f (f (map hd buf) z) (map tl buf) = (z', buf')"
          using nonempty False rec.prems by simp
        show "list_all3 (\<lambda>P j xs. Suc i \<le> j \<and> list_all2 P [Suc i..<j] xs) Ps js (map tl buf)"
          using False rec.prems
          by (auto simp: list_all3_map elim!: list_all3_mono_strong dest: list.rel_sel[THEN iffD1])
        show "U (Suc i) (f (map hd buf) z)"
          using more False rec.prems
          by (auto 0 4 simp: list_all3_map intro!: rec.prems(4) list_all3_list_all2I
              elim!: list_all3_mono_strong dest: list.rel_sel[THEN iffD1])
        show "\<And>k xs z. Suc i \<le> k \<Longrightarrow> Suc k \<le> Mini (Suc i) js \<Longrightarrow>
          list_all2 (\<lambda>P. P k) Ps xs \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs z)"
          by (rule rec.prems(4)) (auto simp: Mini_def)
      qed
    qed
  qed
qed

lemma mbufnt_take_induct[consumes 5, case_names base step]:
  assumes "mbufnt_take f z buf nts = (z', buf', nts')"
    and "wf_mbufn i js Ps buf"
    and "list_all2 R [i..<j] nts"
    and "\<And>k. k \<in> set js \<Longrightarrow> k \<le> j"
    and "U i z"
    and "\<And>k xs t z. i \<le> k \<Longrightarrow> Suc k \<le> Mini j js \<Longrightarrow>
      list_all2 (\<lambda>P x. P k x) Ps xs \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs t z)"
  shows "U (Mini (i + length nts) js) z'"
  using assms
proof (induction f z buf nts arbitrary: i z' buf' nts' rule: mbufnt_take.induct)
  case (1 f z buf nts)
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  note mbufnt_take.simps[simp del]
  from 1(2-6) have "i = Min (set js)" if "js \<noteq> []" "nts = []"
    using that unfolding wf_mbufn_def using wf_mbufn_in_set_Mini[OF 1(3)]
    by (fastforce simp: Mini_def list_all3_Cons neq_Nil_conv)
  with 1(2-7) list_all2_hdD[OF 1(4)] show ?case
    unfolding wf_mbufn_def using wf_mbufn_in_set_Mini[OF 1(3)] wf_mbufn_notin_set[OF 1(3)]
    by (subst (asm) mbufnt_take.simps)
      (auto simp add: Mini_def list.rel_map Suc_le_eq
        elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated]
        list_all3_mono_strong[THEN list_all3_list_all2I[of _ _ js]] list_all2_hdD
        dest!: 1(1)[rotated, OF _ wf_mbufn_map_tl[OF 1(3)] * _ 1(7)] split: prod.split if_splits)
qed

lemma mbuf2_take_add':
  assumes eq: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
    and pre: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and rm: "rel_mapping (\<le>) P P'"
    and xs: "list_all2 (\<lambda>i r. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i r. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> P' V j' n R \<phi> \<psi> buf'"
    and "list_all2 (\<lambda>i Z. \<exists>X Y.
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
      qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) Y \<and>
      Z = f X Y)
      [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' \<psi> j')] zs"
  using pre rm unfolding wf_mbuf2'_def
  by (force intro!: mbuf2_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> rm])+


lemma mbuft2_take_add':
  assumes eq: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
    and pre: "wf_mbuft2' \<sigma> P V j n R \<phi> \<alpha> I \<beta> buf"
    and rm: "rel_mapping (\<le>) P P'"
    and xs: "list_all2 (\<lambda>i r. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
      [progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j'] ys"
    and "j \<le> j'"
  shows "wf_mbuft2' \<sigma> P' V j' n R \<phi> \<alpha> I \<beta> buf'"
  and "list_all2 (\<lambda>i Z. \<exists>X V_Y Y.
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
      wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and>
      Z = f X (V_Y, Y))
      [min (progress \<sigma> P \<phi> j) (progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..<min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j')] zs"
proof -
  have progress:
    "Monitor.progress \<sigma> P \<phi> j \<le> Monitor.progress \<sigma> P' \<phi> j'"
    "Monitor.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j \<le> Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j'"
    using progress_mono_gen[OF \<open>j \<le> j'\<close> rm] progress_mono_gen[OF \<open>j \<le> j'\<close> rm, of _ "(formula.Trigger \<alpha> I \<beta>)"]
    by auto

  have wf_add: "wf_mbuf2 (min (Monitor.progress \<sigma> P \<phi> j) (Monitor.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)) (Monitor.progress \<sigma> P' \<phi> j') (Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j')
   (\<lambda>i. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>))
   (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r) (mbuf2_add xs ys buf)"
    using wf_mbuf2_add[OF pre[unfolded wf_mbuft2'_def] xs ys progress]
    by auto

  show
    "wf_mbuft2' \<sigma> P' V j' n R \<phi> \<alpha> I \<beta> buf'"
    "list_all2 (\<lambda>i Z. \<exists>X V_Y Y.
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
      wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and>
      Z = f X (V_Y, Y))
      [min (progress \<sigma> P \<phi> j) (progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..<min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j')] zs"
    unfolding wf_mbuft2'_def
    using mbuf2_take_eqD[OF eq wf_add]
    by auto
qed

lemma mbuf2t_take_add':
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) nts = (z', buf', nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and pre_buf: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (r). qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> P' V j' n R \<phi> \<psi> buf'"
    and "wf_ts \<sigma> P' j' \<phi> \<psi> nts'"
  using pre_buf pre_nts bounded rm unfolding wf_mbuf2'_def wf_ts_def
  by (auto intro!: mbuf2t_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> rm]
      progress_le_gen)


lemma ok_0_atms: "ok 0 mr \<Longrightarrow> regex.atms (from_mregex mr []) = {}"
  by (induct mr) auto

lemma ok_0_progress: "ok 0 mr \<Longrightarrow> progress_regex \<sigma> P (from_mregex mr []) j = j"
  by (drule ok_0_atms) (auto simp: progress_regex_def)

lemma atms_empty_atms: "safe_regex m g r \<Longrightarrow> atms r = {} \<longleftrightarrow> regex.atms r = {}"
  by (induct r rule: safe_regex_induct) (auto split: if_splits simp: cases_Neg_iff)

lemma atms_empty_progress: "safe_regex m g r \<Longrightarrow> atms r = {} \<Longrightarrow> progress_regex \<sigma> P r j = j"
  by (drule atms_empty_atms) (auto simp: progress_regex_def)

lemma to_mregex_empty_progress: "safe_regex m g r \<Longrightarrow> to_mregex r = (mr, []) \<Longrightarrow>
  progress_regex \<sigma> P r j = j"
  using from_mregex_eq ok_0_progress to_mregex_ok atms_empty_atms by fastforce

lemma progress_regex_le: "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress_regex \<sigma> P r j \<le> j"
  by (auto intro!: progress_le_gen simp: Min_le_iff progress_regex_def)

lemma Neg_acyclic: "formula.Neg x = x \<Longrightarrow> P"
  by (induct x) auto

lemma case_Neg_in_iff: "x \<in> (case y of formula.Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<longleftrightarrow> y = formula.Neg x"
  by (cases y) auto

lemma atms_nonempty_progress:
  "safe_regex m g r \<Longrightarrow> atms r \<noteq> {} \<Longrightarrow> (\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` atms r = (\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` regex.atms r"
  by (frule atms_empty_atms; simp)
    (auto 0 3 simp: atms_def image_iff case_Neg_in_iff elim!: disjE_Not2 dest: safe_regex_safe_formula)

lemma to_mregex_nonempty_progress: "safe_regex m g r \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow> \<phi>s \<noteq> [] \<Longrightarrow>
  progress_regex \<sigma> P r j = (MIN \<phi>\<in>set \<phi>s. progress \<sigma> P \<phi> j)"
  using atms_nonempty_progress to_mregex_ok unfolding progress_regex_def by fastforce

lemma to_mregex_progress: "safe_regex m g r \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow>
  progress_regex \<sigma> P r j = (if \<phi>s = [] then j else (MIN \<phi>\<in>set \<phi>s. progress \<sigma> P \<phi> j))"
  using to_mregex_nonempty_progress to_mregex_empty_progress unfolding progress_regex_def by auto

lemma mbufnt_take_add':
  assumes eq: "mbufnt_take f z (mbufn_add xss buf) nts = (z', buf', nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and safe: "safe_regex m g r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and pre_buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j'] nts"
    and xss: "list_all3 list_all2
     (map (\<lambda>\<phi> i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r) \<phi>s)
     (map2 upt (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s) (map (\<lambda>\<phi>. progress \<sigma> P' \<phi> j') \<phi>s)) xss"
    and "j \<le> j'"
  shows "wf_mbufn' \<sigma> P' V j' n R r buf'"
    and "wf_ts_regex \<sigma> P' j' r nts'"
  using pre_buf pre_nts bounded rm mr safe xss \<open>j \<le> j'\<close>  unfolding wf_mbufn'_def wf_ts_regex_def
  using atms_empty_progress[of m g r] to_mregex_ok[OF mr]
  by (auto 0 3 simp: list.rel_map to_mregex_empty_progress to_mregex_nonempty_progress Mini_def
      intro: progress_mono_gen[OF \<open>j \<le> j'\<close> rm] list.rel_refl_strong progress_le_gen
      dest: list_all2_lengthD elim!: mbufnt_take_eqD[OF eq wf_mbufn_add])

lemma mbuf2t_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) nts = (z', buf', nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and pre_buf: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (r). qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
    and base: "U (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) z"
    and step: "\<And>k X Y z. min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) \<le> k \<Longrightarrow>
      Suc k \<le> progress \<sigma> P' \<phi> j' \<Longrightarrow> Suc k \<le> progress \<sigma> P' \<psi> j' \<Longrightarrow>
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<phi>) X \<Longrightarrow>
      qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<psi>) Y \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f X Y (\<tau> \<sigma> k) z)"
  shows "U (min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' \<psi> j')) z'"
  using pre_buf pre_nts bounded rm unfolding wf_mbuf2'_def
  by (blast intro!: mbuf2t_take_induct[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> rm]
      progress_le_gen base step)

lemma mbufnt_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbufnt_take f z (mbufn_add xss buf) nts = (z', buf', nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and safe: "safe_regex m g r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and pre_buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j'] nts"
    and xss: "list_all3 list_all2
     (map (\<lambda>\<phi> i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r) \<phi>s)
     (map2 upt (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s) (map (\<lambda>\<phi>. progress \<sigma> P' \<phi> j') \<phi>s)) xss"
    and "j \<le> j'"
    and base: "U (progress_regex \<sigma> P r j) z"
    and step: "\<And>k Xs z. progress_regex \<sigma> P r j \<le> k \<Longrightarrow> Suc k \<le> progress_regex \<sigma> P' r j' \<Longrightarrow>
      list_all2 (\<lambda>\<phi> (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<phi>) r) \<phi>s Xs \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f Xs (\<tau> \<sigma> k) z)"
  shows "U (progress_regex \<sigma> P' r j') z'"
  using pre_buf pre_nts bounded rm \<open>j \<le> j'\<close> to_mregex_progress[OF safe mr, of \<sigma> P' j'] to_mregex_empty_progress[OF safe, of mr \<sigma> P j] base
  unfolding wf_mbufn'_def mr prod.case
  by (fastforce dest!: mbufnt_take_induct[OF eq wf_mbufn_add[OF _ xss] pre_nts, of U]
      simp: list.rel_map le_imp_diff_is_add ac_simps Mini_def
      intro: progress_mono_gen[OF \<open>j \<le> j'\<close> rm] list.rel_refl_strong progress_le_gen
      intro!: base step  dest: list_all2_lengthD split: if_splits)

lemma progress_Until_le: "progress \<sigma> P (Formula.Until \<phi> I \<psi>) j \<le> min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)"
  by (auto simp: trans_le_add1 intro!: cInf_lower)

lemma progress_MatchF_le: "progress \<sigma> P (Formula.MatchF I r) j \<le> progress_regex \<sigma> P r j"
  by (auto simp: trans_le_add1 progress_regex_def intro!: cInf_lower)

lemma list_all2_upt_Cons: "P a x \<Longrightarrow> list_all2 P [Suc a..<b] xs \<Longrightarrow> Suc a \<le> b \<Longrightarrow>
  list_all2 P [a..<b] (x # xs)"
  by (simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma list_all2_upt_append: "list_all2 P [a..<b] xs \<Longrightarrow> list_all2 P [b..<c] ys \<Longrightarrow>
  a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> list_all2 P [a..<c] (xs @ ys)"
  by (induction xs arbitrary: a) (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma list_all3_list_all2_conv: "list_all3 R xs xs ys = list_all2 (\<lambda>x. R x x) xs ys"
  by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth)

lemma map_split_map: "map_split f (map g xs) = map_split (f o g) xs"
  by (induct xs) auto

lemma map_split_alt: "map_split f xs = (map (fst o f) xs, map (snd o f) xs)"
  by (induct xs) (auto split: prod.splits)

lemma fv_formula_of_constraint: "fv (formula_of_constraint (t1, p, c, t2)) = fv_trm t1 \<union> fv_trm t2"
  by (induction "(t1, p, c, t2)" rule: formula_of_constraint.induct) simp_all

lemma (in maux) wf_mformula_wf_set: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_set n (Formula.fv \<phi>')"
  unfolding wf_set_def
proof (induction rule: wf_mformula.induct)
  case (AndRel P V n R \<phi> \<phi>' \<psi>' conf)
  then show ?case by (auto simp: fv_formula_of_constraint dest!: subsetD)
next
  case (And_Release I \<phi>' \<psi>' P V n R aux \<alpha>')
  then show ?case using release_fvi(3) by auto
next
  case (Ands P V n R l l_pos l_neg l' buf A_pos A_neg)
  from Ands.IH have "\<forall>\<phi>'\<in>set (l_pos @ map remove_neg l_neg). \<forall>x\<in>fv \<phi>'. x < n"
    unfolding list_all2_iff
    by (metis (no_types, lifting) case_prodD in_set_impl_in_set_zip2)
  then have "\<forall>\<phi>'\<in>set (l_pos @ l_neg). \<forall>x\<in>fv \<phi>'. x < n"
    using fv_remove_neg
    by fastforce
  then show ?case using Ands by auto
next
  case (Agg P V b n R \<phi> \<phi>' y f g0 \<omega>)
  then have "Formula.fvi_trm b f \<subseteq> Formula.fvi b \<phi>'"
    by (auto simp: fvi_trm_iff_fv_trm[where b=b] fvi_iff_fv[where b=b])
  with Agg show ?case by (auto 0 3 simp: Un_absorb2 fvi_iff_fv[where b=b])
next
  case (Release_0)
  then show ?case using release_fvi(1) by auto
next
  case (MatchP r P V n R \<phi>s mr mrs buf nts I aux)
  then obtain \<phi>s' where conv: "to_mregex r = (mr, \<phi>s')" by blast
  with MatchP have "\<forall>\<phi>'\<in>set \<phi>s'. \<forall>x\<in>fv \<phi>'. x < n"
    by (simp add: list_all2_conv_all_nth all_set_conv_all_nth[of \<phi>s'])
  with conv show ?case
    by (simp add: to_mregex_ok[THEN conjunct1] fv_regex_alt[OF \<open>safe_regex _ _ r\<close>])
next
  case (MatchF r  P V n R \<phi>s mr mrs buf nts I aux)
  then obtain \<phi>s' where conv: "to_mregex r = (mr, \<phi>s')" by blast
  with MatchF have "\<forall>\<phi>'\<in>set \<phi>s'. \<forall>x\<in>fv \<phi>'. x < n"
    by (simp add: list_all2_conv_all_nth all_set_conv_all_nth[of \<phi>s'])
  with conv show ?case
    by (simp add: to_mregex_ok[THEN conjunct1] fv_regex_alt[OF \<open>safe_regex _ _ r\<close>])
qed (auto simp: fvi_Suc split: if_splits)

lemma qtable_mmulti_join:
  assumes pos: "list_all3 (\<lambda>A Qi X. qtable n A P Qi X \<and> wf_set n A) A_pos Q_pos L_pos"
    and neg: "list_all3 (\<lambda>A Qi X. qtable n A P Qi X \<and> wf_set n A) A_neg Q_neg L_neg"
    and C_eq: "C = \<Union>(set A_pos)" and L_eq: "L = L_pos @ L_neg"
    and "A_pos \<noteq> []" and fv_subset: "\<Union>(set A_neg) \<subseteq> \<Union>(set A_pos)"
    and restrict_pos: "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> list_all (\<lambda>A. P (restrict A x)) A_pos"
    and restrict_neg: "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> list_all (\<lambda>A. P (restrict A x)) A_neg"
    and Qs: "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow>
      list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos Q_pos \<and>
      list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg Q_neg"
  shows "qtable n C P Q (mmulti_join n A_pos A_neg L)"
proof (rule qtableI)
  from pos have 1: "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_pos L_pos"
    by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth qtable_def)
  moreover from neg have "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
    by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth qtable_def)
  ultimately have L: "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) (L_pos @ L_neg)"
    by (rule list_all2_appendI)
  note in_join_iff = mmulti_join_correct[OF \<open>A_pos \<noteq> []\<close> L]
  from 1 have take_eq: "take (length A_pos) (L_pos @ L_neg) = L_pos"
    by (auto dest!: list_all2_lengthD)
  from 1 have drop_eq: "drop (length A_pos) (L_pos @ L_neg) = L_neg"
    by (auto dest!: list_all2_lengthD)

  note mmulti_join.simps[simp del]
  show "table n C (mmulti_join n A_pos A_neg L)"
    unfolding C_eq L_eq table_def by (simp add: in_join_iff)
  show "Q x" if "x \<in> mmulti_join n A_pos A_neg L" "wf_tuple n C x" "P x" for x
    using that(2,3)
  proof (rule Qs[THEN iffD2, OF _ _ conjI])
    have pos': "list_all2 (\<lambda>A. (\<in>) (restrict A x)) A_pos L_pos"
      and neg': "list_all2 (\<lambda>A. (\<notin>) (restrict A x)) A_neg L_neg"
      using that(1) unfolding L_eq in_join_iff take_eq drop_eq by simp_all
    show "list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos Q_pos"
      using pos pos' restrict_pos that(2,3)
      by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length qtable_def)
    have fv_subset': "\<And>i. i < length A_neg \<Longrightarrow> A_neg ! i \<subseteq> C"
      using fv_subset unfolding C_eq by (auto simp: Sup_le_iff)
    show "list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg Q_neg"
      using neg neg' restrict_neg that(2,3)
      by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length qtable_def
          wf_tuple_restrict_simple[OF _ fv_subset'])
  qed
  show "x \<in> mmulti_join n A_pos A_neg L" if "wf_tuple n C x" "P x" "Q x" for x
    unfolding L_eq in_join_iff take_eq drop_eq
  proof (intro conjI)
    from that have pos': "list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos Q_pos"
      and neg': "list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg Q_neg"
      using Qs[THEN iffD1] by auto
    show "wf_tuple n (\<Union>A\<in>set A_pos. A) x"
      using \<open>wf_tuple n C x\<close> unfolding C_eq by simp
    show "list_all2 (\<lambda>A. (\<in>) (restrict A x)) A_pos L_pos"
      using pos pos' restrict_pos that(1,2)
      by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length qtable_def
          C_eq wf_tuple_restrict_simple[OF _ Sup_upper])
    show "list_all2 (\<lambda>A. (\<notin>) (restrict A x)) A_neg L_neg"
      using neg neg' restrict_neg that(1,2)
      by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length qtable_def)
  qed
qed

lemma nth_filter: "i < length (filter P xs) \<Longrightarrow>
  (\<And>i'. i' < length xs \<Longrightarrow> P (xs ! i') \<Longrightarrow> Q (xs ! i')) \<Longrightarrow> Q (filter P xs ! i)"
  by (metis (lifting) in_set_conv_nth set_filter mem_Collect_eq)

lemma nth_partition: "i < length xs \<Longrightarrow>
  (\<And>i'. i' < length (filter P xs) \<Longrightarrow> Q (filter P xs ! i')) \<Longrightarrow>
  (\<And>i'. i' < length (filter (Not \<circ> P) xs) \<Longrightarrow> Q (filter (Not \<circ> P) xs ! i')) \<Longrightarrow> Q (xs ! i)"
  by (metis (no_types, lifting) in_set_conv_nth set_filter mem_Collect_eq comp_apply)

lemma qtable_bin_join:
  assumes "qtable n A P Q1 X" "qtable n B P Q2 Y" "\<not> b \<Longrightarrow> B \<subseteq> A" "C = A \<union> B"
    "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> P (restrict A x) \<and> P (restrict B x)"
    "\<And>x. b \<Longrightarrow> wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A x) \<and> Q2 (restrict B x)"
    "\<And>x. \<not> b \<Longrightarrow> wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A x) \<and> \<not> Q2 (restrict B x)"
  shows "qtable n C P Q (bin_join n A X b B Y)"
  using qtable_join[OF assms] bin_join_table[of n A X B Y b] assms(1,2)
  by (auto simp add: qtable_def)

lemma restrict_update: "y \<notin> A \<Longrightarrow> y < length x \<Longrightarrow> restrict A (x[y:=z]) = restrict A x"
  unfolding restrict_def by (auto simp add: nth_list_update)

lemma qtable_assign:
  assumes "qtable n A P Q X"
    "y < n" "insert y A = A'" "y \<notin> A"
    "\<And>x'. wf_tuple n A' x' \<Longrightarrow> P x' \<Longrightarrow> P (restrict A x')"
    "\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> Q' (x[y:=Some (f x)])"
    "\<And>x'. wf_tuple n A' x' \<Longrightarrow> P x' \<Longrightarrow> Q' x' \<Longrightarrow> Q (restrict A x') \<and> x' ! y = Some (f (restrict A x'))"
  shows "qtable n A' P Q' ((\<lambda>x. x[y:=Some (f x)]) ` X)" (is "qtable _ _ _ _ ?Y")
proof (rule qtableI)
  from assms(1) have "table n A X" unfolding qtable_def by simp
  then show "table n A' ?Y"
    unfolding table_def wf_tuple_def using assms(2,3)
    by (auto simp: nth_list_update)
next
  fix x'
  assume "x' \<in> ?Y" "wf_tuple n A' x'" "P x'"
  then obtain x where "x \<in> X" and x'_eq: "x' = x[y:=Some (f x)]" by blast
  then have "wf_tuple n A x"
    using assms(1) unfolding qtable_def table_def by blast
  then have "y < length x" using assms(2) by (simp add: wf_tuple_def)
  with \<open>wf_tuple n A x\<close> have "restrict A x' = x"
    unfolding x'_eq by (simp add: restrict_update[OF assms(4)] restrict_idle)
  with \<open>wf_tuple n A' x'\<close> \<open>P x'\<close> have "P x"
    using assms(5) by blast
  with \<open>wf_tuple n A x\<close> \<open>x \<in> X\<close> have "Q x"
    using assms(1) by (elim in_qtableE)
  with \<open>wf_tuple n A x\<close> \<open>P x\<close> show "Q' x'"
    unfolding x'_eq by (rule assms(6))
next
  fix x'
  assume "wf_tuple n A' x'" "P x'" "Q' x'"
  then have "wf_tuple n A (restrict A x')"
    using assms(3) by (auto intro!: wf_tuple_restrict_simple)
  moreover have "P (restrict A x')"
    using \<open>wf_tuple n A' x'\<close> \<open>P x'\<close> by (rule assms(5))
  moreover have "Q (restrict A x')" and y: "x' ! y = Some (f (restrict A x'))"
    using \<open>wf_tuple n A' x'\<close> \<open>P x'\<close> \<open>Q' x'\<close> by (auto dest!: assms(7))
  ultimately have "restrict A x' \<in> X" by (intro in_qtableI[OF assms(1)])
  moreover have "x' = (restrict A x')[y:=Some (f (restrict A x'))]"
    using y assms(2,3) \<open>wf_tuple n A (restrict A x')\<close> \<open>wf_tuple n A' x'\<close>
    by (auto simp: list_eq_iff_nth_eq wf_tuple_def nth_list_update nth_restrict)
  ultimately show "x' \<in> ?Y" by simp
qed

lemma sat_the_update: "y \<notin> fv \<phi> \<Longrightarrow> Formula.sat \<sigma> V (map the (x[y:=z])) i \<phi> = Formula.sat \<sigma> V (map the x) i \<phi>"
  by (rule sat_fv_cong) (metis map_update nth_list_update_neq)

lemma progress_constraint: "progress \<sigma> P (formula_of_constraint c) j = j"
  by (induction rule: formula_of_constraint.induct) simp_all

lemma qtable_filter:
  assumes "qtable n A P Q X"
    "\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<and> R x \<longleftrightarrow> Q' x"
  shows "qtable n A P Q' (Set.filter R X)" (is "qtable _ _ _ _ ?Y")
proof (rule qtableI)
  from assms(1) have "table n A X"
    unfolding qtable_def by simp
  then show "table n A ?Y"
    unfolding table_def wf_tuple_def by simp
next
  fix x
  assume "x \<in> ?Y" "wf_tuple n A x" "P x"
  with assms show "Q' x" by (auto elim!: in_qtableE)
next
  fix x
  assume "wf_tuple n A x" "P x" "Q' x"
  with assms show "x \<in> Set.filter R X" by (auto intro!: in_qtableI)
qed

lemma eval_constraint_sat_eq: "wf_tuple n A x \<Longrightarrow> fv_trm t1 \<subseteq> A \<Longrightarrow> fv_trm t2 \<subseteq> A \<Longrightarrow>
  \<forall>i\<in>A. i < n \<Longrightarrow> eval_constraint (t1, p, c, t2) x =
    Formula.sat \<sigma> V (map the x) i (formula_of_constraint (t1, p, c, t2))"
  by (induction "(t1, p, c, t2)" rule: formula_of_constraint.induct)
    (simp_all add: meval_trm_eval_trm)

declare progress_le_gen[simp]

definition wf_envs :: "
  \<comment> \<open>\<sigma> : trace\<close>
  Formula.trace \<Rightarrow>
  \<comment> \<open>j : current ts\<close>
  nat \<Rightarrow>
  \<comment> \<open>\<delta> : number of new ts that are read in one step\<close>
  nat \<Rightarrow>
  \<comment> \<open>P : number of tables outputted for \<phi> (p/let) after reading in  j      timestamps (progress)\<close>
  (Formula.name \<rightharpoonup> nat) \<Rightarrow>
  \<comment> \<open>P': number of tables outputted for \<phi> (p/let) after reading in (j + \<delta>) timestamps (progress)\<close>
  (Formula.name \<rightharpoonup> nat) \<Rightarrow>
  \<comment> \<open>V: tables of \<phi>\<close>
  (Formula.name \<rightharpoonup> (nat \<Rightarrow> event_data list set)) \<Rightarrow>
  \<comment> \<open>db: tables of \<sigma> and for predicates p (let overrides predicates in trace)\<close>
  Formula.database \<Rightarrow>
  bool"
  where
"wf_envs \<sigma> j \<delta> P P' V db =
  (dom V = dom P \<and>
  \<comment> \<open>db should contain all of P (until j) and the ones in between j and j + \<delta> => until j + \<delta>\<close>
   Mapping.keys db = dom P \<union> (\<Union>k \<in> {j ..< j + \<delta>}. {p. p \<in> fst ` \<Gamma> \<sigma> k}) \<and>
  \<comment> \<open>the number of tables outputted after j+\<delta> has to be greater or equal to the number of tables outputted after j\<close>
   rel_mapping (\<le>) P P' \<and>
  \<comment> \<open>at j no more than j tables could have been outputted\<close>
   pred_mapping (\<lambda>i. i \<le> j) P \<and>
  \<comment> \<open>at j+\<delta> no more than j+\<delta> tables could have been outputted\<close>
   pred_mapping (\<lambda>i. i \<le> j + \<delta>) P' \<and>
  \<comment> \<open>the keys of db without the ones until j equals the databases in between j and j + \<delta>\<close>
   (\<forall>p \<in> Mapping.keys db - dom P. the (Mapping.lookup db p) = map (\<lambda>k. {ts. (p, ts) \<in> \<Gamma> \<sigma> k}) [j ..< j + \<delta>]) \<and>
   (\<forall>p \<in> dom P. list_all2 (\<lambda>i X. X = the (V p) i) [the (P p)..<the (P' p)] (the (Mapping.lookup db p))))"


lift_definition mk_db :: "(Formula.name \<times> event_data list) set \<Rightarrow> Formula.database" is
  "\<lambda>X p. (if p \<in> fst ` X then Some [{ts. (p, ts) \<in> X}] else None)" .

lemma wf_envs_mk_db: "wf_envs \<sigma> j 1 Map.empty Map.empty Map.empty (mk_db (\<Gamma> \<sigma> j))"
  unfolding wf_envs_def mk_db_def
  by transfer (force split: if_splits simp: image_iff rel_mapping_alt)

lemma wf_envs_update:
  assumes wf_envs: "wf_envs \<sigma> j \<delta> P P' V db"
    and m_eq: "m = Formula.nfv \<phi>"
    and in_fv: "{0 ..< m} \<subseteq> fv \<phi>"
    and xs: "list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>) (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>))
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
  shows "wf_envs \<sigma> j \<delta> (P(p \<mapsto> progress \<sigma> P \<phi> j)) (P'(p \<mapsto> progress \<sigma> P' \<phi> (j + \<delta>)))
    (V(p \<mapsto> \<lambda>i. {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>}))
    (Mapping.update p (map (image (map the)) xs) db)"
  unfolding wf_envs_def
proof (intro conjI ballI, goal_cases)
  case 3
  from assms show ?case
    by (auto simp: wf_envs_def pred_mapping_alt progress_le progress_mono_gen
        intro!: rel_mapping_map_upd)
next
  case (6 p')
  with assms show ?case by (cases "p' \<in> dom P") (auto simp: wf_envs_def lookup_update')
next
  case (7 p')
  from xs in_fv have "list_all2 (\<lambda>x y. map the ` y = {v. length v = m \<and> Formula.sat \<sigma> V v x \<phi>})
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    by (elim list.rel_mono_strong) (auto 0 3 simp: wf_tuple_def nth_append
      elim!: in_qtableE in_qtableI intro!: image_eqI[where x="map Some _"])
  moreover have "list_all2 (\<lambda>i X. X = the (V p') i) [the (P p')..<the (P' p')] (the (Mapping.lookup db p'))"
    if "p \<noteq> p'"
  proof -
    from that 7 have "p' \<in> dom P" by simp
    with wf_envs show ?thesis by (simp add: wf_envs_def)
  qed
  ultimately show ?case
    by (simp add: list.rel_map image_iff lookup_update')
qed (use assms in \<open>auto simp: wf_envs_def subset_iff\<close>)

lemma wf_envs_P_simps[simp]:
   "wf_envs \<sigma> j \<delta> P P' V db \<Longrightarrow> pred_mapping (\<lambda>i. i \<le> j) P"
   "wf_envs \<sigma> j \<delta> P P' V db \<Longrightarrow> pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
   "wf_envs \<sigma> j \<delta> P P' V db \<Longrightarrow> rel_mapping (\<le>) P P'"
  unfolding wf_envs_def by auto

lemma wf_envs_progress_le[simp]:
   "wf_envs \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P \<phi> j \<le> j"
   "wf_envs \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) \<le> j + \<delta>"
  unfolding wf_envs_def by auto

lemma wf_envs_progress_regex_le[simp]:
   "wf_envs \<sigma> j \<delta> P P' V db \<Longrightarrow> progress_regex \<sigma> P r j \<le> j"
   "wf_envs \<sigma> j \<delta> P P' V db \<Longrightarrow> progress_regex \<sigma> P' r (j + \<delta>) \<le> j + \<delta>"
  unfolding wf_envs_def by (auto simp: progress_regex_le)

lemma wf_envs_progress_mono[simp]:
   "wf_envs \<sigma> j \<delta> P P' V db \<Longrightarrow> a \<le> b \<Longrightarrow> progress \<sigma> P \<phi> a \<le> progress \<sigma> P' \<phi> b"
  unfolding wf_envs_def
  by (auto simp: progress_mono_gen)

lemma qtable_wf_tuple_cong: "qtable n A P Q X \<Longrightarrow> A = B \<Longrightarrow> (\<And>v. wf_tuple n A v \<Longrightarrow> P v \<Longrightarrow> Q v = Q' v) \<Longrightarrow> qtable n B P Q' X"
  unfolding qtable_def table_def by blast

lemma list_all2_replicate[simp]: "list_all2 R (replicate m x) xs \<longleftrightarrow> length xs = m \<and> (\<forall>i < m. R x (xs ! i))"
  by (auto simp: list_all2_conv_all_nth)

lemma list_all2_replicate2[simp]: "list_all2 R xs (replicate m x) \<longleftrightarrow> length xs = m \<and> (\<forall>i < m. R (xs ! i) x)"
  by (auto simp: list_all2_conv_all_nth)

lemma (in maux) wf_mformula_release: "wf_mformula \<sigma> j P V n R \<phi> (release_safe_0 \<phi>' I \<psi>') \<Longrightarrow> (case \<phi> of (MOr \<alpha> \<beta> buf) \<Rightarrow> True | _ \<Rightarrow> False)"
  by (cases rule: wf_mformula.cases) (auto simp add: release_safe_0_def split: if_splits)

lemma zip_map_el: "(i, x) \<in> set (zip xs (map f xs)) \<Longrightarrow> x = f i"
  by (metis fst_conv in_set_zip nth_map snd_conv)

lemma drop_filter_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memR I (mt - t)) xs = drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memR I (mt - t)) xs = drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
    using Cons
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR I (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = (filter (\<lambda>(t, _). memR I (mt - t)) xs)"
      by auto
    moreover have "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = (drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). memR I (mt - t)) xs)"
      by auto
    show ?thesis
    proof (cases "length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)")
      case 0
      then show ?thesis using IH by auto
    next
      case (Suc nat)
      then have drop_IH: "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = drop nat xs"
        using filter_IH
        by auto
      then show ?thesis
      proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR I (mt - t)) db")
        case True
        then have "(length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) = 0"
          using True mem
          by (simp add: prod.case_eq_if)
        then have "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x#xs"
          using mem
          by auto
        moreover have "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = x#xs"
          using True mem
          by auto
        ultimately show ?thesis
          by auto
      next
        case False
        then obtain j where j_props: "((\<lambda>(t, _). \<not>memR I (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
          by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
        then have "((\<lambda>(t, _). \<not>memR I (mt - t)) ((x#xs)!(Suc j)))"
          by auto
        moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
          using Cons(2) j_props
          by auto
        ultimately have "((\<lambda>(t, _). \<not>memR I (mt - t)) x)" using memR_antimono by auto
        then show ?thesis using mem by auto
      qed
    qed
  qed
qed

lemma take_filter_not_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
    using Cons
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR I (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)"
      by auto
    moreover have "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x#(take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)"
      by auto
    then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) (x#xs)"
      by auto
    show ?thesis
    proof (cases "length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)")
      case 0
      then show ?thesis by auto
    next
      case (Suc nat)
      then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x # (take nat xs)"
        using takeWhile_IH
        by auto
      then show ?thesis
      proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR I (mt - t)) db")
        case True
        then have "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = []"
          using filter_IH
          by (simp add: case_prod_beta')
        then show ?thesis using takeWhile_IH by auto
      next
        case False
        then obtain j where j_props: "((\<lambda>(t, _). \<not>memR I (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
          by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
        then have "((\<lambda>(t, _). \<not>memR I (mt - t)) ((x#xs)!(Suc j)))"
          by auto
        moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
          using Cons(2) j_props
          by auto
        ultimately have "((\<lambda>(t, _). \<not>memR I (mt - t)) x)" using memR_antimono by auto
        then show ?thesis using not_mem by auto
      qed
    qed
  qed
qed

lemma zip_P: "\<And>xs P. (\<forall>(i,x) \<in> set (zip [0..<length xs] xs). P x) = (\<forall>x \<in> set xs. P x)"
  by (metis case_prodD case_prodI2 diff_zero in_set_impl_in_set_zip2 length_upt set_zip_rightD)
lemma zip_idx: "\<And>xs P. \<forall>(i,x) \<in> set (zip [0..<length xs] xs). x = xs!i"
  by (metis (mono_tags, lifting) case_prodI2 map_nth zip_map_el)

lemma memR_impl_pred:
  shows "memR (args_ivl args) (\<tau> \<sigma> k - j) \<Longrightarrow> memR (args_ivl args) (\<tau> \<sigma> (k - 1) - j)"
proof -
  have "\<tau> \<sigma> (k - 1) \<le> \<tau> \<sigma> k"
    by auto
  then have "\<tau> \<sigma> (k - 1) - j \<le> \<tau> \<sigma> k - j"
    by linarith
  then show memR_impl: "memR (args_ivl args) (\<tau> \<sigma> k - j) \<Longrightarrow> memR (args_ivl args) (\<tau> \<sigma> (k - 1) - j)"
    using memR_antimono[of "args_ivl args"]
    by auto
qed

lemma max_memR:
  assumes A_def: "A = {j. j\<le>k \<and> memR (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> j)}"
  shows "k = Max A"
proof -
  have "k \<in> A"
    unfolding A_def
    by auto
  moreover {
    assume "\<exists>k' \<in> A. k' > k"
    then obtain k' where k'_props: "k' \<in> A" "k' > k"
      by auto
    then have "False"
      unfolding A_def
      by auto
  }
  ultimately show k_eq: "k = Max A"
    unfolding A_def
    by (metis (no_types, lifting) Max_eqI finite_nat_set_iff_bounded_le le_less_linear)
qed
lemma eq_memR:
  assumes non_empty: "A \<noteq> {}"
  assumes A_def: "A = {j. j<k \<and> memR (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> j)}"
  shows "A = {Min A..Max A}"
proof -
  have A_props: "finite A" "A \<noteq> {}"
    using non_empty
    unfolding A_def
    by auto

  define j where "j = Min A"

  have "j \<in> A"
    using A_props
    unfolding j_def
    by auto
  then have j_props: "j \<le> k" "memR (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> j)"
    unfolding A_def
    by auto

  have "\<And>x. x \<in> {Min A..Max A} \<Longrightarrow> x \<in> A"
  proof -
    fix x
    assume assm: "x \<in> {Min A..Max A}"
    then have "x \<le> Max A" by auto
    moreover have "Max A \<in> A" using A_props by auto
    ultimately have "x < k"
      unfolding A_def
      by auto
    moreover have "memR (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> x)"
    proof -
      have "x \<ge> j"
        using j_def assm
        by auto
      then have "\<tau> \<sigma> j \<le> \<tau> \<sigma> x"
        by auto
      then have "\<tau> \<sigma> k - \<tau> \<sigma> j \<ge> \<tau> \<sigma> k - \<tau> \<sigma> x"
        by linarith
      then show ?thesis
        using j_props memR_antimono
        by auto
    qed
    ultimately show "x \<in> A"
      unfolding A_def
      by auto
  qed
  moreover have "\<And>x. x < Min A \<Longrightarrow> x \<notin> A"
    using A_props
    by auto
  moreover have "\<And>x. x > Max A \<Longrightarrow> x \<notin> A"
    using A_props
    by auto
  ultimately have A_mem: "\<And>x. (x \<in> {Min A..Max A}) = (x \<in> A)"
    by (meson A_props Min_eq_iff atLeastAtMost_iff eq_Max_iff)
  then show "A = {Min A..Max A}"
    by blast
qed


lemma proj_tuple_nth:
  assumes "i < length t" "bs!i" "length bs = length t"
  shows "(proj_tuple bs t)!i = t ! i"
  using assms
proof (induction bs t arbitrary: i rule: proj_tuple.induct)
  case (2 bs a as)
  then show ?case by (cases i) (auto)
next
  case (3 bs a as)
  then show ?case by (cases i) (auto)
qed (auto)

lemma rel_mono_zip:
  assumes before: "list_all2 P1 x y"
  assumes impl: "(\<And>a b. (a, b) \<in> set (zip x y) \<Longrightarrow> P1 a b \<Longrightarrow> P2 a b)"
  shows "list_all2 P2 x y"
proof -
  have eq_len: "length x = length y"
    using before
    unfolding list_all2_iff
    by auto
  moreover have "\<And>a b. (a, b)\<in>set (zip x y) \<Longrightarrow> P2 a b"
  proof -
    fix a b
    assume "(a, b)\<in>set (zip x y)"
    then show "P2 a b"
      using before impl
      unfolding list_all2_iff
      by auto
  qed

  ultimately show ?thesis
    unfolding list_all2_iff
    by auto
qed

lemma (in maux) update_trigger:
  assumes wf_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux k"
  assumes qtable_X: "qtable n (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<gamma>) X"
  assumes qtable_Y: "qtable n (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<beta>) Y"
  assumes args_n: "args_n args = n"
  assumes args_L: "args_L args = fv \<gamma>"
  assumes args_R: "args_R args = fv \<beta>"
  shows "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
proof -
  have table:
    "table (args_n args) (args_L args) X"
    "table (args_n args) (args_R args) Y"
    using qtable_X qtable_Y args_n args_L args_R
    unfolding qtable_def
    by auto

  obtain cur auxlist where wf_trigger_before:
    "Formula.fv \<gamma> \<subseteq> Formula.fv \<beta>"
    "valid_mtaux args cur aux (filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist)"
    "cur = (if k = 0 then 0 else \<tau> \<sigma> (k - 1))"
    "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist"
    "length auxlist = k"
    "\<forall>(i, (t, l, r)) \<in> set (zip [0..<length auxlist] auxlist).
      k \<noteq> 0 \<and>
      t = \<tau> \<sigma> i \<and>
      t \<le> \<tau> \<sigma> (k - 1) \<and>
      qtable (args_n args) (Formula.fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l  \<and>
      qtable (args_n args) (Formula.fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
     "
    "\<forall>i.
        k \<noteq> 0 \<and>
        i \<le> (k - 1)
        \<longrightarrow>
        (\<exists>X. (\<tau> \<sigma> i, X) = auxlist!i)
    "
    using wf_trigger
    unfolding wf_trigger_aux_def
    by auto

  define cur' where "cur' = \<tau> \<sigma> k"
  define auxlist' where "auxlist' = auxlist @ [(cur', X, Y)]"

  have "\<tau> \<sigma> (k - 1) \<le> \<tau> \<sigma> k"
    by auto
  moreover have "\<forall>x \<in> set auxlist. fst x \<le> \<tau> \<sigma> (k-1)"
    using wf_trigger_before(6) zip_P[of auxlist "\<lambda>x. fst x \<le> \<tau> \<sigma> (k-1)"]
    by auto
  ultimately have auxlist_leq: "\<forall>x \<in> set auxlist. fst x \<le> \<tau> \<sigma> k"
    using le_trans by blast
  then have sorted_auxlist': "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'"
    using wf_trigger_before(4)
    unfolding auxlist'_def cur'_def
    by (simp add: sorted_wrt_append)
  then have sorted:
    "sorted (map fst auxlist)"
    "sorted (map fst auxlist')"
    using wf_trigger_before(4)
    by (auto simp add: sorted_map)

  have auxlist_len: "length auxlist' = Suc k"
    using wf_trigger_before(5)
    unfolding auxlist'_def
    by auto

  have auxlist_props:
    "\<forall>(i, (t, l, r)) \<in> set (zip [0..<length auxlist'] auxlist').
      Suc k \<noteq> 0 \<and>
      t = \<tau> \<sigma> i \<and>
      t \<le> \<tau> \<sigma> k \<and>
      qtable (args_n args) (Formula.fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l  \<and>
      qtable (args_n args) (Formula.fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
     "
  proof -
    {
      fix i t l r
      assume assm: "(i, (t, l, r)) \<in> set (zip [0..<length auxlist'] auxlist')"
      then have i_mem: "i \<in> {0..<length auxlist'}"
        using set_zip_leftD
        by fastforce
      have
        "Suc k \<noteq> 0 \<and>
        t = \<tau> \<sigma> i \<and>
        t \<le> \<tau> \<sigma> k \<and>
        qtable (args_n args) (Formula.fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l  \<and>
        qtable (args_n args) (Formula.fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r"
      proof (cases "i < length auxlist")
        case True
        then have "(i, (t, l, r)) \<in> set (zip [0..<length auxlist] auxlist)"
          using assm zip_idx[of auxlist']
          unfolding auxlist'_def
          by simp
        then have
          "t = \<tau> \<sigma> i \<and>
           t \<le> \<tau> \<sigma> (k - 1) \<and>
           qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
           qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r"
          using wf_trigger_before(6)
          by auto
        then show ?thesis
          using True wf_trigger_before(5)
          by auto
      next
        case False
        then have i_eq: "i = length auxlist"
          using i_mem
          unfolding auxlist'_def
          by auto
        then have "(t, l, r) = (cur', X, Y)"
          using assm zip_idx[of auxlist']
          unfolding auxlist'_def
          by auto
        then show ?thesis
          using qtable_X qtable_Y args_n wf_trigger_before(5) i_eq
          unfolding cur'_def
          by auto
      qed
    }
    then show ?thesis by auto
  qed

  have auxlist_mem:
    "\<forall>i.
        Suc k \<noteq> 0 \<and>
        i \<le> k
        \<longrightarrow>
        (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
    "
  proof -
    {
      fix i
      assume assms: "Suc k \<noteq> 0" "i \<le> k"
      then have "(\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)"
      proof (cases "i < k")
        case True
        then have "\<exists>X. (\<tau> \<sigma> i, X) = auxlist!i"
          using wf_trigger_before(7)
          by auto
        then obtain X' where "(\<tau> \<sigma> i, X') = auxlist!i"
          by auto
        then have "(\<tau> \<sigma> i, X') = auxlist'!i"
          using nth_append[of auxlist "[(cur', X, Y)]" i] wf_trigger_before(5) True
          unfolding auxlist'_def
          by auto
        then show ?thesis
          using exI[of "\<lambda>X'. (\<tau> \<sigma> i, X') = auxlist' ! i"]
          by auto
      next
        case False
        then have "i = length auxlist' - 1" using assms wf_trigger_before(5) unfolding auxlist'_def by auto
        then have "(cur', X, Y) = auxlist' ! i"
          unfolding auxlist'_def
          by auto
        then show ?thesis
          unfolding cur'_def
          using exI[of "\<lambda>X'. (\<tau> \<sigma> i, X') = auxlist' ! i" "(X, Y)"] assms(2) False
          by auto
      qed
    }
    then show ?thesis by auto
  qed

  have "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (cur - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (cur' - t))) =
        (\<lambda>(t, _). memR (args_ivl args) (cur - t) \<and> memR (args_ivl args) (cur' - t))"
    by auto
  moreover have "(\<lambda>(t, _). memR (args_ivl args) (cur - t) \<and> memR (args_ivl args) (cur' - t)) = (\<lambda>(t, _). memR (args_ivl args) (cur' - t))"
    using wf_trigger_before(3)
    unfolding cur'_def
    by (metis memR_impl_pred memR_zero zero_diff)
  ultimately have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (cur - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (cur' - t))) = (\<lambda>(t, _). memR (args_ivl args) (cur' - t))"
    by metis

  have filter_simp:"(filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist) @ [(cur', X, Y)]) =
        (filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) (auxlist @ [(cur', X, Y)]))"
    unfolding filter_filter
    by (auto simp add: filter_simp)

  have "valid_mtaux args cur' (update_mtaux args cur' X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist) @ [(cur', X, Y)])"
    using wf_trigger_before(3) valid_update_mtaux[of cur cur' args X Y aux "(filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist)", OF _ table wf_trigger_before(2)]
    unfolding cur'_def
    by auto
  then have "valid_mtaux args cur' (update_mtaux args cur' X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) (auxlist'))"
    unfolding auxlist'_def
    using filter_simp
    by auto
  then have valid_mtaux:
    "Formula.fv \<gamma> \<subseteq> Formula.fv \<beta>"
    "valid_mtaux args cur' (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) auxlist')"
    "cur' = (if (Suc k) = 0 then 0 else \<tau> \<sigma> k)"
    using wf_trigger_before(1)
    unfolding auxlist'_def cur'_def Let_def
    by (auto simp add: filter_simp split: if_splits prod.splits)

  then show "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
    using sorted_auxlist' auxlist_props auxlist_mem auxlist_len
    unfolding wf_trigger_aux_def diff_Suc_1
    by blast
qed

lemma (in maux) trigger_sat_equiv:
  assumes restr: "mem_restr R x"
  assumes wf_x: "wf_tuple (args_n args) (args_R args) x"
  assumes pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = formula.Neg \<gamma>"
  assumes args_n: "args_n args = n"
  assumes args_ivl: "args_ivl args = I"
  assumes args_L: "args_L args = fv \<gamma>"
  assumes args_R: "args_R args = fv \<beta>"
  assumes fvi_subset: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>"
  assumes fv_l_n: "\<forall>x\<in>fv \<beta>. x < n"
  assumes valid_mtaux: "valid_mtaux args (\<tau> \<sigma> k) (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
  assumes sorted: "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'"
  assumes auxlist_len: "length auxlist' = Suc k"
  assumes auxlist_props: "(\<forall>(i, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist').
       Suc k \<noteq> 0 \<and>
       t = \<tau> \<sigma> i \<and>
       t \<le> \<tau> \<sigma> k \<and>
       qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
       qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
    )"
   assumes auxlist_mem: "(\<forall>i.
        Suc k \<noteq> 0 \<and>
        i \<le> k
        \<longrightarrow>
        (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
    )"
   assumes non_empty: "length (filter (\<lambda> (t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist') > 0"
   shows "x \<in> snd (trigger_results args (\<tau> \<sigma> k) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')) = Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)"
proof -
  have sorted: "sorted (map fst auxlist')"
    using sorted sorted_map
    by blast

  define offset where "offset = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
  then have offset_leq: "offset \<le> length auxlist'"
    by auto

  define auxlist'' where "auxlist'' = (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
  then have auxlist''_eq: "auxlist'' = drop offset auxlist'"
    using drop_filter_memR[OF sorted, of "args_ivl args" "\<tau> \<sigma> k"]
    unfolding offset_def
    by auto

  have auxlist'_filter_sum: "length (filter (\<lambda>(t, _). memR (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist') + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist') = length auxlist'"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) ((\<tau> \<sigma> k) - t))" auxlist']
    by (simp add: case_prod_beta')

  have idx_shift: "\<And>i. i < length auxlist'' \<Longrightarrow> auxlist''!i = auxlist'!(offset + i) \<and> offset + i < length auxlist'"
    unfolding auxlist''_eq
    using nth_drop[OF offset_leq]
    by auto

  have idx_shift_rev: "\<And>i. i <length auxlist' \<Longrightarrow> memR (args_ivl args) (\<tau> \<sigma> k - (fst (auxlist'!i))) \<Longrightarrow> auxlist'!i = auxlist''!(i - offset) \<and> (i - offset) \<in> {0..<length auxlist''}"
  proof -
    fix i
    assume assms: "i <length auxlist'" "memR (args_ivl args) (\<tau> \<sigma> k - (fst (auxlist'!i)))"
    have i_mem: "i \<in> {0..<length auxlist'}"
      using assms(1)
      by auto

    have "i < length auxlist'' + offset"
      using assms auxlist'_filter_sum
      unfolding auxlist''_def offset_def
      by auto
    moreover have "i \<ge> offset"
    proof -
      {
        assume "i < offset"
        then have "auxlist'!i \<in> set (take offset auxlist')"
          using i_mem
          by (metis atLeastLessThan_iff image_eqI nth_image offset_leq)
        moreover have "take offset auxlist' = filter (\<lambda>(t, _). \<not> memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist'"
          using take_filter_not_memR[OF sorted, of "args_ivl args" "\<tau> \<sigma> k"]
          unfolding offset_def
          by auto
        ultimately have "auxlist'!i \<in> set (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
          by auto
        then have "\<not> memR (args_ivl args) (\<tau> \<sigma> k - (fst (auxlist'!i)))"
          by auto
        then have "False" using assms(2) by auto
      }
      then show ?thesis using not_le_imp_less by blast
    qed
    ultimately have "i \<in> {offset..<length auxlist'' + offset}"
      by auto
    then have
      "(i - offset) \<in> {0..<length auxlist''}"
      "auxlist''!(i - offset) = auxlist'!i"
      using idx_shift
      by auto
    then show "auxlist'!i = auxlist''!(i - offset) \<and> (i - offset) \<in> {0..<length auxlist''}"
      by auto
  qed

  have filter_inv: "(filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') = (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist')"
    unfolding auxlist''_def filter_filter
    by (metis (mono_tags, lifting) case_prod_beta')

  define z where "z = snd (trigger_results args (\<tau> \<sigma> k) auxlist'')"



  have z_eq: "z = {
    tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
      (\<forall>i \<in> {0..<(length auxlist'')}.
        let (t, l, r) = auxlist''!i in
        mem (args_ivl args) ((\<tau> \<sigma> k) - t) \<longrightarrow> 
        (
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist'')}.
            join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
          )
        )
      )
    }"
    using non_empty filter_inv
    unfolding z_def
    by auto

  have fv_subset: "fv \<gamma> \<subseteq> fv \<beta> " using fvi_subset by (auto split: if_splits)

  define proj_x where "proj_x = proj_tuple (join_mask (args_n args) (args_L args)) x"
  have len_x: "length x = args_n args"
    using wf_x
    unfolding wf_tuple_def
    by auto
  
  have restr_proj_x: "mem_restr R proj_x"
    using restr
    unfolding proj_x_def proj_tuple_join_mask_restrict[OF len_x]
    by simp

  have len_x_eq: "length (join_mask (args_n args) (args_L args)) = length x"
    using wf_x
    unfolding wf_tuple_def join_mask_def
    by auto

  have join_mask_fv_\<gamma>:
    "i < length (proj_tuple (join_mask (args_n args) (fv \<gamma>)) x) \<and> i < length x \<and> join_mask (args_n args) (fv \<gamma>) ! i"
    if mem: "i \<in> fv \<gamma>" for i
    using wf_x args_n args_R args_L fvi_subset fv_l_n mem
    unfolding wf_tuple_def join_mask_def
    by (auto simp add: proj_tuple_alt split: if_splits)

  have wf_proj_x: "wf_tuple (args_n args) (fv \<gamma>) proj_x"
    using wf_x
    unfolding proj_x_def proj_tuple_join_mask_restrict[OF len_x] args_R args_L
    by (simp add: fv_subset wf_tuple_restrict_simple)

  have proj_sat_equiv: "\<And>j''. Formula.sat \<sigma> V (map the x) j'' \<gamma> = Formula.sat \<sigma> V (map the proj_x) j'' \<gamma>"
    apply (rule sat_fv_cong)
    using nth_map wf_x args_L args_R fv_l_n fvi_subset proj_tuple_nth[OF _ _ len_x_eq]
    unfolding proj_x_def
    by (auto simp add: wf_tuple_def dest!: join_mask_fv_\<gamma>)

  have "x \<in> z = Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)"
  proof (rule iffI)
    assume assm: "x \<in> z"
    then have auxlist_trigger: "(\<forall>i \<in> {0..<(length auxlist'')}.
        let (t, l, r) = auxlist''!i in
        mem (args_ivl args) ((\<tau> \<sigma> k) - t) \<longrightarrow> 
        (
          x \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist'')}.
            join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) x)
          )
        )
      )"
      using z_eq
      by auto
    {
      fix i
      assume i_props: "i \<le> k" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have "\<exists>X. (\<tau> \<sigma> i, X) = auxlist' ! i"
        using allE[OF auxlist_mem, of i]
        by auto
      then obtain l r where lr_props: "(\<tau> \<sigma> i, l, r) = auxlist' ! i"
        by auto
      then have memR: "memR (args_ivl args) (\<tau> \<sigma> k - (fst (auxlist' ! i)))"
        using i_props[folded args_ivl]
        by (metis fstI)

      have i_mem: "i < length auxlist'"
        using i_props(1) auxlist_len
        by auto

      define j where "j = i - offset"

      have j_props:
        "auxlist' ! i = auxlist'' ! j"
        "j \<in> {0..<length auxlist''}"
        using idx_shift_rev[OF i_mem memR]
        unfolding j_def
        by auto

      then have lr_j_props:
        "auxlist'' ! j = (\<tau> \<sigma> i, l, r)"
        "mem (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using i_props(2) lr_props args_ivl
        by auto

      have "(let (t, l, r) = auxlist'' ! j
            in mem (args_ivl args) (\<tau> \<sigma> k - t) \<longrightarrow>
            x \<in> r \<or> (\<exists>j\<in>{j<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x))
        )"
        using ballE[OF auxlist_trigger, of j] j_props(2)
        by blast
      then have "x \<in> r \<or> (\<exists>j\<in>{j<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x))"
        using lr_j_props
        by auto
      moreover {
        assume x_mem: "x \<in> r"
        have "(i, \<tau> \<sigma> i, l, r)\<in>set (zip [0..<length auxlist'] auxlist')"
          using lr_props i_mem in_set_conv_nth
          by fastforce
        then have "qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r"
          using auxlist_props
          by auto
        then have "Formula.sat \<sigma> V (map the x) i \<beta>"
          using x_mem restr 
          unfolding qtable_def
          by auto
      }
      moreover {
        assume "\<exists>k\<in>{j<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! k)) (proj_tuple (join_mask (args_n args) (args_L args)) x)"
        then obtain j' where j'_props:
          "j'\<in>{j<..<length auxlist''}"
          "join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j')) (proj_tuple (join_mask (args_n args) (args_L args)) x)"
          by blast

        define j'' where "j'' = offset + j'"

        have "length auxlist'' = length auxlist' - offset"
          using auxlist'_filter_sum
          unfolding offset_def auxlist''_def
          by auto
        then have "j'\<in>{i - offset<..<length auxlist' - offset}"
          using j'_props(1)
          unfolding j_def
          by auto
        then have j''_mem: "j'' \<in> {i<..<length auxlist'}"
          unfolding j''_def
          by auto

        obtain t l r where tlr_eq: "(t, l, r) = auxlist'' ! j'"
          by (metis prod.collapse)
        moreover have "((fst \<circ> snd) (auxlist'' ! j')) = l"
          by (metis comp_def fst_conv snd_conv tlr_eq)
        ultimately have join_cond: "join_cond (args_pos args) l (proj_tuple (join_mask (args_n args) (args_L args)) x)"
          using j'_props(2)
          by auto
        
        have j'_l: "j'<length auxlist''"
          using j'_props
          by auto
        have k_shift: "auxlist'' ! j' = auxlist' ! (j'')"
          using idx_shift[OF j'_l]
          unfolding j''_def
          by auto
        then have tlr_eq': "(t, l, r) = auxlist' ! (j'')"
          using tlr_eq
          by auto
        then have "(j'', t, l, r)\<in>set (zip [0..<length auxlist'] auxlist')"
          using j'_l j''_mem
          using in_set_zip
          by fastforce
        then have qtable: "qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j'' \<gamma>) l"
          using auxlist_props
          by auto

        have "Formula.sat \<sigma> V (map the x) j'' \<alpha>"
        proof (cases "args_pos args")
          case True
          have mem: "proj_x \<in> l"
            using True join_cond
            unfolding proj_x_def
            by auto
          then have "Formula.sat \<sigma> V (map the proj_x) j'' \<gamma>"
            using qtable restr_proj_x
            unfolding qtable_def
            by auto
          then show ?thesis
            using proj_sat_equiv True pos
            by auto
        next
          case False
          then have not_mem: "proj_x \<notin> l"
            using join_cond
            unfolding proj_x_def
            by auto
          
          have "\<not>Formula.sat \<sigma> V (map the x) j'' \<gamma> "
            using not_mem qtable restr_proj_x proj_sat_equiv wf_proj_x
            unfolding qtable_def
            by blast
          then show ?thesis
            using False pos
            by auto
        qed
        moreover have "j'' \<in> {i <.. k}"
          using j''_mem auxlist_len
          by auto
        ultimately have "\<exists>k \<in> {i <.. k}. Formula.sat \<sigma> V (map the x) k \<alpha>"
          by auto
      }
      ultimately have "Formula.sat \<sigma> V (map the x) i \<beta> \<or> (\<exists>k \<in> {i <.. k}. Formula.sat \<sigma> V (map the x) k \<alpha>)"
        by auto
    }
    then show "Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)"
      by auto
  next
    assume assm: "Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)"
    then have sat: "\<forall>j\<le>k. (mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)) \<longrightarrow> (Formula.sat \<sigma> V (map the x) j \<beta> \<or> (\<exists>k \<in> {j <.. k}. Formula.sat \<sigma> V (map the x) k \<alpha>))"
      by auto

    have wf: "wf_tuple (args_n args) (args_R args) x"
      using wf_x
      by auto

    have "\<forall>i\<in>{0..<length auxlist''}.
      let (t, l, r) = auxlist'' ! i in
        mem (args_ivl args) (\<tau> \<sigma> k - t) \<longrightarrow>
        x \<in> r \<or>
        (\<exists>j\<in>{i<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x))"
    proof -
      {
        fix i
        define t where "t = fst (auxlist'' ! i)"
        define l where "l = (fst o snd) (auxlist'' ! i)"
        define r where "r = (snd o snd) (auxlist'' ! i)"
        define i' where "i' = offset + i"

        assume assm: "i\<in>{0..<length auxlist''}" "mem (args_ivl args) (\<tau> \<sigma> k - t)"
        
        have i'_props:
          "auxlist'' ! i = auxlist' ! i'"
          "i' < length auxlist'"
          using idx_shift[of i] assm(1)
          unfolding i'_def
          by auto
        moreover have "(t,l,r) = auxlist'' ! i"
          unfolding t_def l_def r_def
          by auto
        moreover obtain X' where X'_props: "(\<tau> \<sigma> i', X') = auxlist' ! i'"
          using allE[OF auxlist_mem, of i' "\<exists>X. (\<tau> \<sigma> i', X) = auxlist' ! i'"] auxlist_len i'_props(2)
          by auto
        ultimately have tlr_props:
          "t = \<tau> \<sigma> i'"
          "(t, l, r) = auxlist' ! i'"
          by (metis fst_conv)+
        then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i')"
          using assm(2) args_ivl
          by auto
        then have "Formula.sat \<sigma> V (map the x) i' \<beta> \<or> (\<exists>k\<in>{i'<..k}. Formula.sat \<sigma> V (map the x) k \<alpha>)"
          using sat i'_props(2) auxlist_len
          by auto
        moreover {
          assume assm: "Formula.sat \<sigma> V (map the x) i' \<beta>"
          have "(i', t, l, r)\<in>set (zip [0..<length auxlist'] auxlist')"
            using i'_props tlr_props(2) in_set_zip
            by fastforce
          then have "qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i' \<beta>) r"
            using auxlist_props
            by auto
          then have "x \<in> r"
            using wf_x[unfolded args_R] restr assm
            unfolding qtable_def
            by auto
        }
        moreover {
          assume "\<exists>k\<in>{i'<..k}. Formula.sat \<sigma> V (map the x) k \<alpha>"
          then obtain j where j_props: "j\<in>{i'<..k}" "Formula.sat \<sigma> V (map the x) j \<alpha>"
            by auto
          obtain t l r where tlr_def: "(t, l, r) = auxlist' ! j"
            by (metis prod_cases3)
          moreover have j_l: "j < length auxlist'"
            using j_props(1) auxlist_len
            by auto
          ultimately have "(j, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist')"
            using in_set_zip by fastforce
          then have qtable: "qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j \<gamma>) l"
            using auxlist_props
            by auto

          define j' where "j' = j - offset"

          have "length auxlist'' + offset = Suc k"
            using auxlist'_filter_sum auxlist_len
            unfolding offset_def auxlist''_def
            by auto
          then have "j\<in>{offset + i<..<length auxlist'' + offset}"
            using j_props(1)
            unfolding i'_def
            by auto
          then have j'_mem: "j' \<in> {i<..<length auxlist''}"
            unfolding j'_def
            by auto
          then have "auxlist'' ! j' = auxlist' ! j"
            using idx_shift
            unfolding j'_def
            by auto
          then have tlr_eq: "(t, l, r) = auxlist'' ! j'"
            using tlr_def
            by auto

          have "\<exists>j\<in>{i<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x)"
          proof (cases "args_pos args")
            case True
            then have sat: "Formula.sat \<sigma> V (map the proj_x) j \<gamma>"
              using j_props pos proj_sat_equiv
              by auto
            then have "proj_x \<in> l"
              using qtable restr_proj_x wf_proj_x
              unfolding qtable_def
              by auto
            then have "proj_x \<in> ((fst \<circ> snd) (auxlist'' ! j'))"
              using tlr_eq
              by (metis comp_def fst_conv snd_conv)
            then have "\<exists>j\<in>{i<..<length auxlist''}. proj_x \<in> ((fst \<circ> snd) (auxlist'' ! j))"
              using j'_mem
              by auto
            then show ?thesis
              using True
              unfolding proj_x_def
              by auto
          next
            case False
            then have sat: "Formula.sat \<sigma> V (map the proj_x) j (Formula.Neg \<gamma>)"
              using j_props pos proj_sat_equiv
              by auto
            then have "proj_x \<notin> l"
              using qtable restr_proj_x wf_proj_x
              unfolding qtable_def
              by auto
            then have "proj_x \<notin> ((fst \<circ> snd) (auxlist'' ! j'))"
              using tlr_eq
              by (metis comp_def fst_conv snd_conv)
            then have "\<exists>j\<in>{i<..<length auxlist''}. proj_x \<notin> ((fst \<circ> snd) (auxlist'' ! j))"
              using j'_mem
              by auto
            then show ?thesis
              using False
              unfolding proj_x_def
              by auto
          qed
        }
        ultimately have "x \<in> r \<or>
         (\<exists>j\<in>{i<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x))"
          by blast
      }
      then show ?thesis
        unfolding Let_def
        by (auto split: prod.splits) fastforce
    qed
    then show "x \<in> z"
      using wf
      unfolding z_eq
      by auto
  qed
  moreover have "fv \<beta> = fst (trigger_results args (\<tau> \<sigma> k) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist'))"
    using non_empty args_R filter_inv
    unfolding auxlist''_def trigger_results.simps
    by auto
  ultimately show ?thesis
    using non_empty
    unfolding z_def auxlist''_def
    by auto
qed

lemma (in maux) meval:
  assumes "wf_mformula \<sigma> j P V n R \<phi> \<phi>'" "wf_envs \<sigma> j \<delta> P P' V db"
  shows "case meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> of (xs, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i (r). qtable n (Formula.fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>') r)
    [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
  using assms
proof (induction P V n R \<phi> \<phi>' arbitrary: db P' rule: wf_mformula.induct)
  case (Eq t1 t2 n P V R)
  then show ?case
    by (auto simp add: ball_Un intro: wf_mformula.intros[unfolded fvi.simps] table_eq_rel eq_rel_eval_trm
        in_eq_rel qtable_empty qtable_unit_table intro!: qtableI)
next
  case (neq_Var x n P V R)
  then show ?case
    by (auto simp add: ball_Un intro: wf_mformula.intros[unfolded fvi.simps] table_eq_rel eq_rel_eval_trm
        in_eq_rel qtable_empty qtable_unit_table intro!: qtableI)
next
  case (Pred e tms n P V R)
  then show ?case
  proof (cases "e \<in> dom P")
    case True
    with Pred(3) have e_props: "e \<in> Mapping.keys db" "e \<in> dom P'" "e \<in> dom V"
      "list_all2 (\<lambda>i X. X = the (V e) i) [the (P e)..<the (P' e)]
         (the (Mapping.lookup db e))" unfolding wf_envs_def rel_mapping_alt by blast+
    show ?thesis
      using True e_props Pred(1-2)
      by (fastforce intro!: wf_mformula.Pred qtableI bexI[where P="\<lambda>x. _ = tabulate x 0 n", OF refl]
      elim!: list.rel_mono_strong bexI[rotated] dest: ex_match
      simp: list.rel_map table_def match_wf_tuple in_these_eq match_eval_trm image_iff
        list.map_comp keys_dom_lookup)
  next
    note Pred(1)
    moreover
    case False
    moreover
    from False Pred(3) have e_not_mem: "e \<notin> dom P'" "e \<notin> dom V"
      unfolding wf_envs_def rel_mapping_alt by auto
    moreover
    from False Pred(3) have *: "e \<in> (\<Union>k \<in> {j ..< j + \<delta>}. fst ` \<Gamma> \<sigma> k) \<longleftrightarrow> e \<in> Mapping.keys db"
      unfolding wf_envs_def by auto
    from False Pred(3) have
      "e \<in> Mapping.keys db \<Longrightarrow> Mapping.lookup db e = Some (map (\<lambda>k. {ts. (e, ts) \<in> \<Gamma> \<sigma> k}) [j ..< j + \<delta>])"
      unfolding wf_envs_def keys_dom_lookup by (metis Diff_iff domD option.sel)
    with * have db_props: "(case Mapping.lookup db e of None \<Rightarrow> replicate \<delta> {} | Some xs \<Rightarrow> xs) =
      map (\<lambda>k. {ts. (e, ts) \<in> \<Gamma> \<sigma> k}) [j ..< j + \<delta>]"
      by (cases "e \<in> (\<Union>k \<in> {j ..< j + \<delta>}. fst ` \<Gamma> \<sigma> k)")
        (auto 0 3 simp: image_iff keys_dom_lookup list.rel_eq[symmetric] list.rel_map
         intro: list.rel_refl split: option.splits)
    define xs where "xs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MPred e tms))"
    define \<alpha> where "\<alpha> = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MPred e tms))"

    have pair_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MPred e tms) = (xs, \<alpha>)"
      unfolding xs_def \<alpha>_def
      by auto
    have \<alpha>_eq: "\<alpha> = (MPred e tms)"
      unfolding Pred(1) \<alpha>_def meval.simps
      by auto
    have wf: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<alpha> (formula.Pred e tms)"
      using wf_mformula.Pred[OF Pred(1-2)]
      unfolding \<alpha>_eq
      by auto

    have xs_eq: "xs = map (\<lambda>X. (\<lambda>f. Table.tabulate f 0 n) ` Option.these
        (match tms ` X)) (case Mapping.lookup db e of None \<Rightarrow> replicate (length (map (\<tau> \<sigma>) [j..<j + \<delta>])) empty_table | Some xs \<Rightarrow> xs)"
      unfolding xs_def
      by auto
    then have "length xs = \<delta>"
      using db_props
      by (auto split: option.splits)
    then have "length [Monitor.progress \<sigma> P (formula.Pred e tms) j..<Monitor.progress \<sigma> P' (formula.Pred e tms) (j + \<delta>)] =
               length xs"
      using False e_not_mem
      by auto
    moreover have "\<forall>(i, r) \<in> set (zip [Monitor.progress \<sigma> P (formula.Pred e tms) j..<Monitor.progress \<sigma> P' (formula.Pred e tms) (j + \<delta>)] xs).
      qtable n (fv (formula.Pred e tms)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Pred e tms)) r"
    proof -
      {
        fix i r
        assume assm: "(i, r) \<in> set (zip [Monitor.progress \<sigma> P (formula.Pred e tms) j..<Monitor.progress \<sigma> P' (formula.Pred e tms) (j + \<delta>)] xs)"
        then have mems:
          "i \<in> set [Monitor.progress \<sigma> P (formula.Pred e tms) j..<Monitor.progress \<sigma> P' (formula.Pred e tms) (j + \<delta>)]"
          "r \<in> set xs"
          by (meson set_zip_leftD set_zip_rightD)+

        have i_mem: "i \<in> set [j..<(j + \<delta>)]"
          using False e_not_mem mems(1)
          unfolding Pred(1)
          by auto
        have assm': "(i, r) \<in> set (zip [j..<(j + \<delta>)] xs)"
          using assm False e_not_mem mems(1)
          unfolding Pred(1)
          by auto
        
        have "qtable n (fv (formula.Pred e tms)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Pred e tms)) r"
        proof (cases "Mapping.lookup db e")
          case None
          then have "xs = replicate (length (map (\<tau> \<sigma>) [j..<j + \<delta>])) ((\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` empty_table))"
            using xs_eq
            by auto
          then have r_eq: "r = {}"
            using mems(2)
            unfolding empty_table_def
            by auto
          then have qtable1:
            "table n (fv (formula.Pred e tms)) r"
            "(\<And>x. x \<in> r \<Longrightarrow> wf_tuple n (fv (formula.Pred e tms)) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) i (formula.Pred e tms))"
            by (auto simp: list.rel_map table_def match_wf_tuple in_these_eq match_eval_trm image_iff)
          
          have \<Gamma>_props: "replicate \<delta> {} = map (\<lambda>k. {ts. (e, ts) \<in> \<Gamma> \<sigma> k}) [j..<j + \<delta>]"
            using None db_props
            by auto
          have qtable2: "(\<And>x. wf_tuple n (fv (formula.Pred e tms)) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) i (formula.Pred e tms) \<Longrightarrow> x \<in> r)"
          proof -
            fix x
            assume assms: "wf_tuple n (fv (formula.Pred e tms)) x" "mem_restr R x" "Formula.sat \<sigma> V (map the x) i (formula.Pred e tms)"
            have "(case V e of
               None \<Rightarrow> (e, map (Formula.eval_trm (map the x)) tms) \<in> \<Gamma> \<sigma> i
             | Some X \<Rightarrow> map (Formula.eval_trm (map the x)) tms \<in> X i)"
              using Pred(1) assms(3)
              by auto
            then have non_empty: "(e, map (Formula.eval_trm (map the x)) tms) \<in> \<Gamma> \<sigma> i"
              using e_not_mem
              by auto
            
            have "{ts. (e, ts) \<in> \<Gamma> \<sigma> i} \<in> set (map (\<lambda>k. {ts. (e, ts) \<in> \<Gamma> \<sigma> k}) [j..<j + \<delta>])"
              using i_mem
              by auto
            moreover have "\<forall>x \<in> set (map (\<lambda>k. {ts. (e, ts) \<in> \<Gamma> \<sigma> k}) [j..<j + \<delta>]). x = {}"
              using \<Gamma>_props
              by (metis in_set_replicate)
            ultimately have "{ts. (e, ts) \<in> \<Gamma> \<sigma> i} = {}"
              using \<Gamma>_props
              by auto
            then show "x \<in> r"
              using non_empty
              by auto
          qed

          show ?thesis
            using qtableI[OF qtable1 qtable2]
            by auto
        next
          case (Some ys)
          then have xs_eq: "xs = map (\<lambda>X. (\<lambda>f. tabulate f 0 n) ` Option.these (match tms ` X)) ys"
            using xs_eq
            by auto
          moreover have ys_eq: "ys = map (\<lambda>k. {ts. (e, ts) \<in> \<Gamma> \<sigma> k}) [j..<j + \<delta>]"
            using Some db_props
            by auto
          ultimately have qtable1:
            "table n (fv (formula.Pred e tms)) r"
            using Pred(1) mems(2)
            by (auto simp: table_def match_wf_tuple in_these_eq)

          have r_eq: "r = (\<lambda>x. tabulate x 0 n) ` Option.these (match tms ` {ts. (e, ts) \<in> \<Gamma> \<sigma> i})"
            using zip_map_el[OF assm'[unfolded xs_eq ys_eq map_map]]
            by auto
           
          have qtable2: "(\<And>x. x \<in> r \<Longrightarrow> wf_tuple n (fv (formula.Pred e tms)) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) i (formula.Pred e tms))"
          proof -
            fix x
            assume "x \<in> r"
            then have "(e, map (Formula.eval_trm (map the x)) tms) \<in> \<Gamma> \<sigma> i"
              using mems(2) i_mem Pred(1) r_eq
              unfolding xs_eq ys_eq
              by (auto dest: ex_match simp: list.rel_map in_these_eq match_eval_trm image_iff)
            then show "Formula.sat \<sigma> V (map the x) i (formula.Pred e tms)"
              using e_not_mem
              by auto
          qed

          have qtable3: "(\<And>x. wf_tuple n (fv (formula.Pred e tms)) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) i (formula.Pred e tms) \<Longrightarrow> x \<in> r)"
          proof -
            fix x
            assume assms: "wf_tuple n (fv (formula.Pred e tms)) x" "mem_restr R x" "Formula.sat \<sigma> V (map the x) i (formula.Pred e tms)"
            then have \<Gamma>_mem: "(e, map (Formula.eval_trm (map the x)) tms) \<in> \<Gamma> \<sigma> i"
              using e_not_mem
              unfolding Pred(1)
              by (auto split: option.splits)
            have wf: "wf_tuple n (\<Union> (fv_trm ` set tms)) x"
              using assms(1)
              unfolding Pred(1)
              by auto
            have fvs: "\<forall>t\<in>set tms. (\<forall>i\<in>fv_trm t. i < n) \<and> (trm.is_Var t \<or> trm.is_Const t)"
              using Pred(1-2)
              by auto
            obtain f where f_props:
              "match tms (map (Formula.eval_trm (map the x)) tms) = Some f"
              "x = tabulate f 0 n"
              using \<Gamma>_mem ex_match[OF wf fvs]
              by auto
            moreover have "match tms (map (Formula.eval_trm (map the x)) tms) \<in> match tms ` {ts. (e, ts) \<in> \<Gamma> \<sigma> i}"
              using \<Gamma>_mem
              by auto
            ultimately have "f \<in> Option.these (match tms ` {ts. (e, ts) \<in> \<Gamma> \<sigma> i})"
              using in_these_eq[of f]
              by auto
            then have "\<exists>x\<in>Option.these (match tms ` {ts. (e, ts) \<in> \<Gamma> \<sigma> i}). tabulate f 0 n = tabulate x 0 n"
              using f_props
              by auto
            then show "x \<in> r"
              using f_props(2)
              unfolding xs_eq ys_eq Pred(1) r_eq
              by auto
          qed

          show ?thesis
            using qtableI[OF qtable1 qtable2 qtable3]
            by auto
        qed
        then have "qtable n (fv (formula.Pred e tms)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Pred e tms)) r"
          using qtableI[of n "(fv (formula.Pred e tms))" r "(mem_restr R)" "(\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Pred e tms))"]
          by auto
      }
      then show ?thesis by auto
    qed
    ultimately have "list_all2 (\<lambda>i. qtable n (fv (formula.Pred e tms)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Pred e tms))) [Monitor.progress \<sigma> P (formula.Pred e tms) j..<Monitor.progress \<sigma> P' (formula.Pred e tms) (j + \<delta>)] xs"
      unfolding list_all2_iff
      by auto
    then show ?thesis
      using wf pair_eq
      by auto
  qed
next
  case (Let P V m \<phi>1 \<phi>1' p n R \<phi>2 \<phi>2' b)
  from Let(1-3,5) have
    1: "wf_mformula \<sigma> j P V m UNIV \<phi>1 \<phi>1'" and
    fv: "m = Formula.nfv \<phi>1'" "{0..<m} \<subseteq> fv \<phi>1'" and
    2: "wf_mformula \<sigma> j (P(p \<mapsto> progress \<sigma> P \<phi>1' j))
      (V(p \<mapsto> \<lambda>i. {v. length v = m \<and> Formula.sat \<sigma> V v i \<phi>1'}))
      n R \<phi>2 \<phi>2'"
    by auto
  obtain xs \<phi>1_new where e1: "meval m (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>1 = (xs, \<phi>1_new)" and
      wf1: "wf_mformula \<sigma> (j + \<delta>) P' V m UNIV \<phi>1_new \<phi>1'" and
      res1: "list_all2 (\<lambda>i (r). qtable m (fv \<phi>1') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>1') r)
       [progress \<sigma> P \<phi>1' j..<progress \<sigma> P' \<phi>1' (j + \<delta>)] xs"
    using Let.IH(1)[OF Let.prems(1)] by (auto simp: eqTrueI[OF mem_restr_UNIV, abs_def])
  from Let.IH(2)[OF wf_envs_update[OF Let.prems(1) fv res1]] wf1 e1 fv
  show ?case unfolding Let by (auto simp: fun_upd_def intro!: wf_mformula.Let)
next
  case (And P V n R \<phi> \<phi>' \<psi> \<psi>' pos \<chi> buf)
  have IH: "case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> of
    (xs, \<phi>\<^sub>n) \<Rightarrow>
      wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
    "case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> of
    (xs, \<phi>\<^sub>n) \<Rightarrow>
      wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<psi>' \<and>
      list_all2 (\<lambda>i. qtable n (fv \<psi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>')) [Monitor.progress \<sigma> P \<psi>' j..<Monitor.progress \<sigma> P' \<psi>' (j + \<delta>)] xs"
    using And.IH[OF And.prems(1)]
    by auto

  have env:
    "rel_mapping (\<le>) P P'"
    "j \<le> j + \<delta>"
    using And.prems
    by auto

  define xs where "xs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"
  define \<phi>'' where "\<phi>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"

  have xtuple_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (xs, \<phi>'')"
    unfolding xs_def \<phi>''_def
    by auto

  have \<phi>_IH:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>'' \<phi>'"
    "list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
    using IH(1)
    by (auto simp add: xtuple_eq)

  define ys where "ys = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi>)"
  define \<psi>'' where "\<psi>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi>)"

  have ytuple_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> = (ys, \<psi>'')"
    unfolding ys_def \<psi>''_def
    by auto

  have \<psi>_IH:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<psi>'' \<psi>'"
    "list_all2 (\<lambda>i. qtable n (fv \<psi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>')) [Monitor.progress \<sigma> P \<psi>' j..<Monitor.progress \<sigma> P' \<psi>' (j + \<delta>)] ys"
    using IH(2)
    by (auto simp add: ytuple_eq)

  define zs where "zs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAnd (fv \<phi>') \<phi> pos (fv \<psi>') \<psi> buf))"
  define \<chi>'' where "\<chi>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAnd (fv \<phi>') \<phi> pos (fv \<psi>') \<psi> buf))"

  have ztuple_eq: "(zs, \<chi>'') = meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAnd (fv \<phi>') \<phi> pos (fv \<psi>') \<psi> buf)"
    unfolding zs_def \<chi>''_def
    by auto

  have zs_eq: "zs = fst (mbuf2_take (\<lambda>(r1) (r2). (bin_join n (fv \<phi>') r1 pos (fv \<psi>') r2)) (mbuf2_add xs ys buf))"
    using xs_def ys_def
    unfolding zs_def meval.simps Let_def
    by (auto simp only: xtuple_eq ytuple_eq split: prod.splits if_splits) (auto)

  define buf' where "buf' = snd (mbuf2_take (\<lambda>(r1) (r2). (bin_join n (fv \<phi>') r1 pos (fv \<psi>') r2)) (mbuf2_add xs ys buf))"

  have mbuf2_take_eq: "mbuf2_take (\<lambda>(r1) (r2). (bin_join n (fv \<phi>') r1 pos (fv \<psi>') r2)) (mbuf2_add xs ys buf) = (zs, buf')"
    using zs_eq buf'_def
    by auto

  have \<chi>''_eq: "\<chi>'' = (MAnd (fv \<phi>') \<phi>'' pos (fv \<psi>') \<psi>'' buf')"
    unfolding \<chi>''_def meval.simps Let_def buf'_def
    by (auto simp only: xtuple_eq ytuple_eq split: prod.splits if_splits) (auto)

  have buf_take_add_IH:
    "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R \<phi>' \<psi>' buf'"
    "list_all2
     (\<lambda>i Z. \<exists>X Y. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>') X \<and>
                   qtable n (fv \<psi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>') Y \<and> Z = bin_join n (fv \<phi>') X pos (fv \<psi>') Y)
     [min (Monitor.progress \<sigma> P \<phi>' j) (Monitor.progress \<sigma> P \<psi>' j)..<min (Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)) (Monitor.progress \<sigma> P' \<psi>' (j + \<delta>))] zs"
    using mbuf2_take_add'[OF mbuf2_take_eq And(4) env(1) \<phi>_IH(2) \<psi>_IH(2) env(2)]
    by auto

  have "wf_mformula \<sigma> (j + \<delta>) P' V n R \<chi>'' \<chi>"
    unfolding \<chi>''_eq
    using wf_mformula.And[OF \<phi>_IH(1) \<psi>_IH(1) And(3) buf_take_add_IH(1)]
    by auto
  moreover have "list_all2 (\<lambda>i. qtable n (fv \<chi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<chi>)) [Monitor.progress \<sigma> P \<chi> j..<Monitor.progress \<sigma> P' \<chi> (j + \<delta>)] zs"
  proof -
    have progress_eq:
      "[min (Monitor.progress \<sigma> P \<phi>' j) (Monitor.progress \<sigma> P \<psi>' j)..<min (Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)) (Monitor.progress \<sigma> P' \<psi>' (j + \<delta>))] =
       [Monitor.progress \<sigma> P \<chi> j..<Monitor.progress \<sigma> P' \<chi> (j + \<delta>)]"
      using And(3)
      by (auto split: if_splits)
    then have "length [Monitor.progress \<sigma> P \<chi> j..<Monitor.progress \<sigma> P' \<chi> (j + \<delta>)] = length zs"
      using buf_take_add_IH(2)
      unfolding list_all2_iff
      by (auto)
    moreover have "\<And>i y. (i, y)\<in>set (zip [Monitor.progress \<sigma> P \<chi> j..<Monitor.progress \<sigma> P' \<chi> (j + \<delta>)] zs) \<Longrightarrow> qtable n (fv \<chi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<chi>) y"
    proof -
      fix i Z
      assume "(i, Z)\<in>set (zip [Monitor.progress \<sigma> P \<chi> j..<Monitor.progress \<sigma> P' \<chi> (j + \<delta>)] zs)"
      then have "(i, Z)\<in>set (zip [min (Monitor.progress \<sigma> P \<phi>' j) (Monitor.progress \<sigma> P \<psi>' j)..<min (Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)) (Monitor.progress \<sigma> P' \<psi>' (j + \<delta>))] zs)"
        using progress_eq
        by auto
      then have "\<exists>X Y. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>') X \<and>
                   qtable n (fv \<psi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>') Y \<and> Z = bin_join n (fv \<phi>') X pos (fv \<psi>') Y"
        using buf_take_add_IH(2)
        unfolding list_all2_iff
        by blast
      then obtain X Y where qtables:
        "qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>') X"
        "qtable n (fv \<psi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>') Y"
        "Z = bin_join n (fv \<phi>') X pos (fv \<psi>') Y"
        by auto

      have fvs:
        "(\<not> pos \<Longrightarrow> fv \<psi>' \<subseteq> fv \<phi>')"
        "fv \<chi> = fv \<phi>' \<union> fv \<psi>'"
        using And(3)
        by (auto split: if_splits)

      have qtable_pos: "(\<And>x. pos \<Longrightarrow>
        wf_tuple n (fv \<chi>) x \<Longrightarrow>
        mem_restr R x \<Longrightarrow>
        Formula.sat \<sigma> V (map the x) i \<chi> = (Formula.sat \<sigma> V (map the (restrict (fv \<phi>') x)) i \<phi>' \<and> Formula.sat \<sigma> V (map the (restrict (fv \<psi>') x)) i \<psi>'))"
        using And(3) sat_the_restrict
        by (auto)

      have qtable_neg_pos: "(\<And>x. \<not> pos \<Longrightarrow>
        wf_tuple n (fv \<chi>) x \<Longrightarrow>
        mem_restr R x \<Longrightarrow>
        Formula.sat \<sigma> V (map the x) i \<chi> = (Formula.sat \<sigma> V (map the (restrict (fv \<phi>') x)) i \<phi>' \<and> \<not> Formula.sat \<sigma> V (map the (restrict (fv \<psi>') x)) i \<psi>'))"
        using And(3) sat_the_restrict
        by (auto)

      show "qtable n (fv \<chi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<chi>) Z"
        unfolding qtables(3)
        using qtable_bin_join[OF qtables(1-2) fvs _ qtable_pos qtable_neg_pos]
        by auto
    qed
    ultimately show ?thesis
      unfolding list_all2_iff
      by auto
  qed
  ultimately show ?case
    using ztuple_eq
    by auto
next
  case (AndAssign P V n R \<phi> \<phi>'' x t conf \<psi>'')
  from AndAssign have
    wf_envs: "wf_envs \<sigma> j \<delta> P P' V db" and
    wf_\<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''" and
    "x < n" and
    "x \<notin> fv \<phi>''" and
    fv_t_subset: "fv_trm t \<subseteq> fv \<phi>''" and
    conf: "(x, t) = conf" and
    \<psi>''_eqs: "\<psi>'' = formula.Eq (trm.Var x) t \<or> \<psi>'' = formula.Eq t (trm.Var x)"
    by auto
  from wf_\<phi> wf_envs obtain xs \<phi>\<^sub>n where
    meval_eq: "meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> = (xs, \<phi>\<^sub>n)" and
    wf_\<phi>\<^sub>n: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>''" and
    xs: "list_all2 (\<lambda>i. qtable n (fv \<phi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>''))
        [progress \<sigma> P \<phi>'' j..<progress \<sigma> P' \<phi>'' (j + \<delta>)] xs"
    by (auto dest!: AndAssign.IH)
  have progress_eqs:
      "progress \<sigma> P (formula.And \<phi>'' \<psi>'') j = progress \<sigma> P \<phi>'' j"
      "progress \<sigma> P' (formula.And \<phi>'' \<psi>'') (j + \<delta>) = progress \<sigma> P' \<phi>'' (j + \<delta>)"
    using \<psi>''_eqs wf_envs_progress_le[OF wf_envs] by (auto)

  show ?case proof (simp add: meval_eq, intro conjI)
    show "wf_mformula \<sigma> (j + \<delta>) P' V n R (MAndAssign \<phi>\<^sub>n conf) (formula.And \<phi>'' \<psi>'')"
      by (rule wf_mformula.AndAssign) fact+
  next
    have "list_all2 (\<lambda>i. qtable n (fv (formula.And \<phi>'' \<psi>'')) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi>'' \<psi>'')))
        [progress \<sigma> P (formula.And \<phi>'' \<psi>'') j..<progress \<sigma> P' (formula.And \<phi>'' \<psi>'') (j + \<delta>)] (map ((`) (eval_assignment conf)) xs)"
      unfolding list.rel_map progress_eqs conf[symmetric] eval_assignment.simps
      using xs
    proof (rule list.rel_mono_strong)
      fix i X
      assume qtable: "qtable n (fv \<phi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'') X"
      then show "qtable n (fv (formula.And \<phi>'' \<psi>'')) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi>'' \<psi>''))
          ((\<lambda>y. y[x := Some (meval_trm t y)]) ` X)"
      proof (rule qtable_assign)
        show "x < n" by fact
        show "insert x (fv \<phi>'') = fv (formula.And \<phi>'' \<psi>'')"
          using \<psi>''_eqs fv_t_subset by (auto)
        show "x \<notin> fv \<phi>''" by fact
      next
        fix v
        assume wf_v: "wf_tuple n (fv (formula.And \<phi>'' \<psi>'')) v" and "mem_restr R v"
        then show "mem_restr R (restrict (fv \<phi>'') v)" by simp

        assume sat: "Formula.sat \<sigma> V (map the v) i (formula.And \<phi>'' \<psi>'')"
        then have A: "Formula.sat \<sigma> V (map the (restrict (fv \<phi>'') v)) i \<phi>''" (is ?A)
          by (simp add: sat_the_restrict)
        have "map the v ! x = Formula.eval_trm (map the v) t"
          using sat \<psi>''_eqs by (auto)
        also have "... = Formula.eval_trm (map the (restrict (fv \<phi>'') v)) t"
          using fv_t_subset by (auto simp: map_the_restrict intro!: eval_trm_fv_cong)
        finally have "map the v ! x = meval_trm t (restrict (fv \<phi>'') v)"
          using meval_trm_eval_trm[of n "fv \<phi>''" "restrict (fv \<phi>'') v" t]
            fv_t_subset wf_v wf_mformula_wf_set[unfolded wf_set_def, OF wf_\<phi>]
          by (fastforce simp: intro!: wf_tuple_restrict)
        then have B: "v ! x = Some (meval_trm t (restrict (fv \<phi>'') v))" (is ?B)
          using \<psi>''_eqs wf_v \<open>x < n\<close> by (auto simp: wf_tuple_def)
        from A B show "?A \<and> ?B" ..
      next
        fix v
        assume wf_v: "wf_tuple n (fv \<phi>'') v" and "mem_restr R v"
          and sat: "Formula.sat \<sigma> V (map the v) i \<phi>''"
        let ?v = "v[x := Some (meval_trm t v)]"
        from sat have A: "Formula.sat \<sigma> V (map the ?v) i \<phi>''"
          using \<open>x \<notin> fv \<phi>''\<close> by (simp add: sat_the_update)
        have "y \<in> fv_trm t \<Longrightarrow> x \<noteq> y" for y
          using fv_t_subset \<open>x \<notin> fv \<phi>''\<close> by auto
        then have B: "Formula.sat \<sigma> V (map the ?v) i \<psi>''"
          using \<psi>''_eqs meval_trm_eval_trm[of n "fv \<phi>''" v t] \<open>x < n\<close>
            fv_t_subset wf_v wf_mformula_wf_set[unfolded wf_set_def, OF wf_\<phi>]
          by (auto simp: wf_tuple_def map_update intro!: eval_trm_fv_cong)
        from A B show "Formula.sat \<sigma> V (map the ?v) i (formula.And \<phi>'' \<psi>'')"
          by (simp)
      qed
    qed
    then show "list_all2 (\<lambda>i. qtable n (fv \<phi>'' \<union> fv \<psi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'' \<and> Formula.sat \<sigma> V (map the v) i \<psi>''))
     [min (Monitor.progress \<sigma> P \<phi>'' j) (Monitor.progress \<sigma> P \<psi>'' j)..<min (Monitor.progress \<sigma> P' \<phi>'' (j + \<delta>)) (Monitor.progress \<sigma> P' \<psi>'' (j + \<delta>))]
     (map ((`) (eval_assignment conf)) xs)"
      by auto
  qed
next
  case (AndRel P V n R \<phi> \<phi>' \<psi>' conf)
  then show ?case
    by (auto simp: progress_constraint progress_le list.rel_map fv_formula_of_constraint
      Un_absorb2 wf_mformula_wf_set[unfolded wf_set_def] split: prod.splits
      dest!: AndRel.IH[of P' db] eval_constraint_sat_eq[THEN iffD2]
      intro!: wf_mformula.AndRel
      elim!: list.rel_mono_strong qtable_filter eval_constraint_sat_eq[THEN iffD1])
next
  case (And_Trigger P V n R \<phi>' \<phi> \<alpha> I \<beta> buf1 \<beta>' args \<gamma> \<gamma>' buf2 nts aux)

  define xs where "xs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>')"
  define \<phi>'' where "\<phi>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>')"
  have xtuple_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>' = (xs, \<phi>'')"
    using xs_def \<phi>''_def
    by auto

  have IH_\<phi>:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>'' \<phi>"
    "list_all2 (\<lambda>i. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>)) [Monitor.progress \<sigma> P \<phi> j..<Monitor.progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    using And_Trigger.IH(1)[OF And_Trigger.prems(1)]
    by (auto simp only: xtuple_eq)

  define as where "as = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>')"
  define \<gamma>'' where "\<gamma>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>')"
  have atuple_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>' = (as, \<gamma>'')"
    using as_def \<gamma>''_def
    by auto

  have IH_\<gamma>:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<gamma>'' \<gamma>"
    "list_all2 (\<lambda>i. qtable n (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>)) [Monitor.progress \<sigma> P \<gamma> j..<Monitor.progress \<sigma> P' \<gamma> (j + \<delta>)] as"
    using And_Trigger.IH(3)[OF And_Trigger.prems(1)]
    by (auto simp only: atuple_eq)

  define bs where "bs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>')"
  define \<beta>'' where "\<beta>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>')"
  have btuple_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>' = (bs, \<beta>'')"
    using bs_def \<beta>''_def
    by auto

  have IH_\<beta>:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<beta>'' \<beta>"
    "list_all2 (\<lambda>i. qtable n (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>)) [Monitor.progress \<sigma> P \<beta> j..<Monitor.progress \<sigma> P' \<beta> (j + \<delta>)] bs"
    using And_Trigger.IH(2)[OF And_Trigger.prems(1)]
    by (auto simp only: btuple_eq)

  define zs where "zs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAndTrigger (fv \<phi>) \<phi>' buf1 args \<gamma>' \<beta>' buf2 nts aux))"
  define \<chi>'' where "\<chi>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAndTrigger (fv \<phi>) \<phi>' buf1 args \<gamma>' \<beta>' buf2 nts aux))"
  have ztuple_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAndTrigger (fv \<phi>) \<phi>' buf1 args \<gamma>' \<beta>' buf2 nts aux) = (zs, \<chi>'')"
    using zs_def \<chi>''_def
    by auto

  from And_Trigger have
        pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = formula.Neg \<gamma>"
    and pos_eq: "safe_formula \<alpha> = args_pos args"
    and \<gamma>: "wf_mformula \<sigma> j P V n R \<gamma>' \<gamma>"
    and \<beta>: "wf_mformula \<sigma> j P V n R \<beta>' \<beta>"
    and fvi_subset: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>"
    and buf: "wf_mbuf2' \<sigma> P V j n R \<gamma> \<beta> buf2"
    and nts: "wf_ts \<sigma> P j \<gamma> \<beta> nts"
    and aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux (Monitor.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = fv \<gamma>"
    and args_R: "args_R args = fv \<beta>"
    and fv_l_n: "\<forall>x\<in>fv \<beta>. x < n"
    and fvs: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>"
    by auto

  have args_props:
    "args_n args = n"
    "args_R args = fv \<alpha> \<union> fv \<beta>"
    "fv \<gamma> = fv \<alpha>"
    using pos args_n args_L args_R fvi_subset
    by (auto split: if_splits)

  define tuple where "tuple = mbuf2t_take (\<lambda>r1 r2 t (zs, aux). let
    aux = update_mtaux args t r1 r2 aux;
    (fv_z, z) = result_mtaux args aux
    in
      (zs @ [(fv_z, z)], aux)
  ) ([], aux) (mbuf2_add as bs buf2) (nts @ map (\<tau> \<sigma>) [j..<j + \<delta>])"

  (*have zs_eq: "zs = fst (fst tuple)"
    unfolding tuple_def zs_def meval. simps Let_def xs_def ys_def
    by (auto split: prod.splits)*)
  define zs' where "zs' = fst (fst tuple)"
  define aux' where "aux' = snd (fst tuple)"
  define buf2' where "buf2' = fst (snd tuple)"
  define nts' where "nts' = snd (snd tuple)"

  have tuple_eq: "tuple = ((zs', aux'), buf2', nts')"
    unfolding zs'_def aux'_def buf2'_def nts'_def Let_def
    by auto

  (*have \<eta>_eq: "\<eta> = MTrigger args \<gamma>' \<beta>' buf' nts' aux'"
    unfolding \<eta>_def meval.simps \<gamma>'_def \<beta>'_def aux'_def buf'_def nts'_def tuple_def xs_def ys_def Let_def
    by (auto split: prod.splits)*)

  have pred_mapping:
    "pred_mapping (\<lambda>i. i \<le> j) P"
    "pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
    "rel_mapping (\<le>) P P'"
    using And_Trigger.prems(1)
    by auto

  from And_Trigger.prems(1) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<gamma> j) (progress \<sigma> P \<beta> j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts
    unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)

  have wf_buf_ts_trigger:
    "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R \<gamma> \<beta> buf2'"
    "wf_ts \<sigma> P' (j + \<delta>) \<gamma> \<beta> nts'"
    using mbuf2t_take_add'[OF tuple_eq[unfolded tuple_def] pred_mapping buf nts_snoc IH_\<gamma>(2) IH_\<beta>(2)]
    by auto

  have \<alpha>_\<gamma>_props: "Formula.fv \<alpha> = Formula.fv \<gamma>" "progress \<sigma> P \<alpha> j = progress \<sigma> P \<gamma> j"
  "progress \<sigma> P' \<alpha> j = progress \<sigma> P' \<gamma> j" for j
    using pos
    by (simp_all split: if_splits)

  have update_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (zs', aux')) (Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)) \<and>
  list_all2 (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
    [progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)] (fst (zs', aux'))"
  unfolding progress_simps \<alpha>_\<gamma>_props
  proof (rule mbuf2t_take_add_induct'[where j=j and j'="j + \<delta>" and z'="(zs', aux')",
      OF tuple_eq[unfolded tuple_def] wf_envs_P_simps[OF And_Trigger.prems(1)] buf nts_snoc],
      goal_cases xs ys _ base step)
    case xs
    then show ?case using IH_\<gamma>(2) by auto
  next
    case ys
    then show ?case using IH_\<beta>(2) by auto
  next
    case base
    then show ?case
      using aux \<alpha>_\<gamma>_props
      unfolding progress_simps 
      by auto
  next
    case (step k X Y acc)
    define zs where "zs = fst acc"
    define aux where "aux = snd acc"
    have z_eq: "acc = (zs, aux)"
      unfolding zs_def aux_def
      by auto

    have table:
      "table (args_n args) (args_L args) X"
      "table (args_n args) (args_R args) Y"
      using step(4-5) args_n args_L args_R
      unfolding qtable_def
      by auto

    have wf_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux k"
      using step(6)
      unfolding aux_def
      by auto
    then have fv_subset: "fv \<gamma> \<subseteq> fv \<beta> "
      unfolding wf_trigger_aux_def
      by auto

    have wf_trigger_aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
      using update_trigger[OF wf_trigger step(4-5) args_n args_L args_R]
      by auto

    then obtain auxlist' where
      valid_mtaux: "valid_mtaux args (\<tau> \<sigma> k) (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')" and
      sorted_wrt: "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'" and
      auxlist_len: "length auxlist' = Suc k" and
      auxlist_props: "(\<forall>(i, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist').
         Suc k \<noteq> 0 \<and>
         t = \<tau> \<sigma> i \<and>
         t \<le> \<tau> \<sigma> k \<and>
         qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
         qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
      )" and
      auxlist_mem: "(\<forall>i.
          Suc k \<noteq> 0 \<and>
          i \<le> k
          \<longrightarrow>
          (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
      )"
      unfolding wf_trigger_aux_def
      by auto

    define zs' where "zs' = fst (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))"
    define aux' where "aux' = snd (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))"

    have "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))) (Suc k)"
      using wf_trigger_aux
      unfolding z_eq Let_def
      by (auto split: prod.splits)
    moreover have "list_all2 (\<lambda>i a. case a of (dfvs, r) \<Rightarrow> wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
     [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k]
     (fst (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux)))"
    proof -
      have aux'_eq: "aux' = update_mtaux args (\<tau> \<sigma> k) X Y aux"
        unfolding aux'_def Let_def
        by (auto split: prod.splits)
      define fv_z where "fv_z = fst (result_mtaux args aux')"
      define z where "z = snd (result_mtaux args aux')"
      define auxlist'' where "auxlist'' = (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"

      have valid_mtaux': "valid_mtaux args (\<tau> \<sigma> k) aux' auxlist''"
        unfolding aux'_eq auxlist''_def
        using valid_mtaux
        by auto
      have z_eq: "z = snd (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have fv_z_eq: "fv_z = fst (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding fv_z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have filter_inv: "(filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') = (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist')"
        unfolding auxlist''_def filter_filter
        by (metis (mono_tags, lifting) case_prod_beta')

      show ?thesis
      proof (cases "0 < length (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')")
        case non_empty: True
        have equiv: "(x \<in> z) = Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)" if
          restr: "mem_restr R x" and
          wf_x: "wf_tuple (args_n args) (args_R args) x"
        for x
          unfolding z_eq auxlist''_def
          using trigger_sat_equiv[OF restr wf_x pos args_n args_ivl args_L args_R fvi_subset fv_l_n valid_mtaux sorted_wrt auxlist_len auxlist_props auxlist_mem non_empty]
          by auto

        have int_non_empty: "\<not>(\<forall>j\<le>k. \<not> mem I (\<tau> \<sigma> k - \<tau> \<sigma> j))"
        proof -
          define auxlist''' where "auxlist''' = (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
          have "auxlist''' \<noteq> []"
            unfolding auxlist'''_def
            using non_empty
            by auto
          then obtain t X where "(t, X) \<in> set auxlist'''"
            by (metis filter_True filter_empty_conv prod.exhaust)
          then have mem:
            "mem (args_ivl args) (\<tau> \<sigma> k - t)"
            "(t, X) \<in> set auxlist'"
            unfolding auxlist'''_def
            by auto
          then obtain i where i_props:
            "i \<in> {0..<length auxlist'}"
            "(t, X) = auxlist'!i"
            by (metis atLeastLessThan_iff in_set_conv_nth zero_le)
          then have "(i, t, X)\<in>set (zip [0..<length auxlist'] auxlist')"
            using mem
            using in_set_zip by fastforce
          then have t_eq: "t = \<tau> \<sigma> i"
            using auxlist_len auxlist_props
            by auto
          show ?thesis
            using mem(1)[unfolded t_eq] i_props(1)[unfolded auxlist_len] not_le_imp_less
            unfolding args_ivl
            by fastforce
        qed

        have "fv_z = args_R args"
          using non_empty filter_inv
          unfolding fv_z_eq auxlist''_def trigger_results.simps
          by auto
        then have fv_z_eq'': "fv_z = fv \<alpha> \<union> fv \<beta>"
          using args_props
          by auto
  
        have "result_mtaux args aux' = trigger_results args (\<tau> \<sigma> k) auxlist''"
          using valid_result_mtaux[OF valid_mtaux]
          unfolding aux'_def auxlist''_def
          by auto
        moreover have "(length (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') > 0)"
          using filter_inv non_empty
          unfolding auxlist''_def
          by auto
        ultimately have z_eq': "z = {
          tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
            (\<forall>i \<in> {0..<(length auxlist'')}.
              let (t, l, r) = auxlist''!i in
              mem (args_ivl args) ((\<tau> \<sigma> k) - t) \<longrightarrow> 
              (
                tuple \<in> r \<or>
                (\<exists>j \<in> {i<..<(length auxlist'')}.
                  join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
                )
              )
            )
          }"
          unfolding z_def
          by auto
  
        have args_R_simp: "args_R args = fv \<alpha> \<union> fv \<beta>"
          using args_L args_R pos fvi_subset
          by (auto split: if_splits)
        have table: "table n (fv \<alpha> \<union> fv \<beta>) z"
          using z_eq'
          unfolding table_def args_R_simp args_n
          by auto
  
        have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
          using equiv args_props
          by auto
  
        have completeness: "\<And>x. wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
          using equiv args_props
          by auto
  
        have qtable_k: "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
          using qtableI[OF table correctness completeness]
          by auto
  
        have zs'_eq: "zs' = zs @ [(fv_z, z)]"
          unfolding zs'_def fv_z_def z_def aux'_eq  Let_def
          by (auto split: prod.splits)
  
        have IH: "list_all2
          (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
          [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs"
          using step(6) zs_def args_props(3)
          by auto
        then have "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] = length zs"
          unfolding list_all2_iff
          by auto
        then have len: "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
          unfolding zs'_eq length_append
          by (simp add: step(1))
  
        moreover have "(\<forall>(i, (dfvs, r)) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] zs').
        wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
        qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
        proof -
          {
            fix i dfvs r
            assume assm: "(i, (dfvs, r)) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] zs')"
            
            have "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] = length zs"
              using step(6) zs_def
              unfolding list_all2_iff
              by auto
            moreover have "[min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] @ [k] =
                           [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k]"
              by (simp add: step(1))
            ultimately have zip_eq:
              "zip ([min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
               zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [(fv_z, z)]"
              unfolding zs'_eq
              using zip_append[of "[min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[(fv_z, z)]"]
              by auto
            {
              assume "(i, (dfvs, r)) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs)"
              then have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using step(6) args_props(3) zs_def
                unfolding list_all2_iff
                by auto
            }
            moreover {
              assume "(i, (dfvs, r)) \<notin> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs)"
              then have eqs: "(i, dfvs, r) = (k, fv_z, z)"
                using assm zip_eq
                by auto
              moreover have "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                using eqs int_non_empty
                unfolding fv_z_eq'' wf_dfvs_def
                by auto
              ultimately have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using qtable_k fv_z_eq''
                by auto
            }
            ultimately have
              "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
              "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              by auto
          }
          then show ?thesis by auto
        qed
  
        ultimately show ?thesis
          unfolding list_all2_iff zs'_def zs_def aux_def
          by (auto split: prod.splits)
        
      next
        case False
        then have empty: "length (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist') = 0"
          by auto

        have int_empty:"\<forall>j\<le>k. \<not> mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
        proof -
          {
            assume "\<exists>j\<le>k. mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
            then obtain j where j_props: "j \<le> k" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
              by blast
            then obtain X where "(\<tau> \<sigma> j, X) = auxlist' ! j"
              using auxlist_mem
              by auto
            then have  "(\<tau> \<sigma> j, X) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
              using auxlist_len j_props args_ivl
              by auto
            then have "False"
              using empty length_pos_if_in_set[of "(\<tau> \<sigma> j, X)"]
              by auto
          }
          then show ?thesis by blast
        qed

        have sat: "\<And>v. Formula.sat \<sigma> V v k (formula.Trigger \<alpha> I \<beta>)"
          using int_empty
          by auto

        have z_eq': "z = {replicate (args_n args) None}"
          using empty filter_inv
          unfolding z_eq auxlist''_def trigger_results.simps
          by auto

        have fv_z_eq': "fv_z = {}"
          using empty filter_inv
          unfolding fv_z_eq auxlist''_def trigger_results.simps
          by auto

        have table: "table n {} z"
          unfolding fv_z_eq' z_eq'
          by (simp add: args_n table_def wf_tuple_unit_table)

        have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n {} x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
          using sat
          by auto
  
        have completeness: "\<And>x. wf_tuple n {} x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
          using sat
          unfolding z_eq'
          by (simp add: args_n wf_tuple_unit_table)
  
        have qtable_k: "qtable n {} (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
          using qtableI[OF table correctness completeness]
          by auto
  
        have zs'_eq: "zs' = zs @ [(fv_z, z)]"
          unfolding zs'_def fv_z_def z_def aux'_eq  Let_def
          by (auto split: prod.splits)
  
        have IH: "list_all2
          (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
          [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs"
          using step(6) zs_def args_props(3)
          by auto
        then have "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] = length zs"
          unfolding list_all2_iff
          by auto
        then have len: "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
          unfolding zs'_eq length_append
          by (simp add: step(1))
  
        moreover have "(\<forall>(i, (dfvs, r)) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] zs').
        wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
        qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
        proof -
          {
            fix i dfvs r
            assume assm: "(i, (dfvs, r)) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] zs')"
            
            have "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] = length zs"
              using step(6) zs_def
              unfolding list_all2_iff
              by auto
            moreover have "[min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] @ [k] =
                           [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k]"
              by (simp add: step(1))
            ultimately have zip_eq:
              "zip ([min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
               zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [(fv_z, z)]"
              unfolding zs'_eq
              using zip_append[of "[min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[(fv_z, z)]"]
              by auto
            {
              assume "(i, (dfvs, r)) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs)"
              then have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using step(6) args_props(3) zs_def
                unfolding list_all2_iff
                by auto
            }
            moreover {
              assume "(i, (dfvs, r)) \<notin> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs)"
              then have eq: "(i, dfvs, r) = (k, fv_z, z)"
                using assm zip_eq
                by auto
              moreover have "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                using sat eq fv_z_eq' int_empty
                unfolding wf_dfvs_def
                by auto
              ultimately have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using qtable_k fv_z_eq'
                by auto
            }
            ultimately have
              "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
              "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              by auto
          }
          then show ?thesis by auto
        qed
  
        ultimately show ?thesis
          unfolding list_all2_iff zs'_def zs_def aux_def
          by (auto split: prod.splits)
      qed
    qed

    ultimately show ?case using args_props(3) by auto
  qed (auto)
  (* same but this time without the conjunction *)
  then have update_trigger:
    "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux' (Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))"
    "list_all2 (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
     [Monitor.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)] zs'"
    by auto

  define tuple' where "tuple' = mbuf2_take (\<lambda>r1 (V_trigger, r2).
      bin_join n (fv \<phi>) r1 True V_trigger r2
  ) (mbuf2_add xs zs' buf1)"

  have zs_eq: "zs = fst tuple'"
    unfolding zs_def meval.simps tuple'_def Let_def
    apply (auto simp only: xtuple_eq atuple_eq btuple_eq tuple_def[unfolded Let_def, symmetric] tuple_eq)
    by (simp add: case_prod_beta')
    
  define buf1' where "buf1' = snd tuple'"

  have tuple'_eq: "tuple' = (zs, buf1')"
    unfolding zs_eq buf1'_def
    by auto

  have \<chi>''_eq: "\<chi>'' = MAndTrigger (fv \<phi>) \<phi>'' buf1' args \<gamma>'' \<beta>'' buf2' nts' aux'"
    unfolding \<chi>''_def meval.simps Let_def
    apply (auto simp only: xtuple_eq atuple_eq btuple_eq tuple_def[unfolded Let_def, symmetric]
        tuple_eq tuple'_def[unfolded Let_def, symmetric] tuple'_eq)
    by (simp add: case_prod_beta')

  have buf_and:
    "wf_mbuft2' \<sigma> P' V (j + \<delta>) n R \<phi> \<alpha> I \<beta> buf1'"
    "list_all2
     (\<lambda>i Z. \<exists>X V_Y Y.
                qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
                wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
                qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and>
                Z = bin_join n (fv \<phi>) X True V_Y Y)
     [min (Monitor.progress \<sigma> P \<phi> j) (Monitor.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..<
      min (Monitor.progress \<sigma> P' \<phi> (j + \<delta>)) (Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))]
     zs"
    using mbuft2_take_add'[OF tuple'_eq[unfolded tuple'_def] And_Trigger(2) pred_mapping(3) IH_\<phi>(2) update_trigger(2)]
    by auto

  have "wf_mformula \<sigma> (j + \<delta>) P' V n R \<chi>'' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))"
    unfolding \<chi>''_eq
    using wf_mformula.And_Trigger[OF IH_\<phi>(1) buf_and(1) And_Trigger(3) IH_\<beta>(1) pos IH_\<gamma>(1) pos_eq args_ivl args_n args_L args_R fv_l_n fvs wf_buf_ts_trigger update_trigger(1)]
    by auto
  moreover have "list_all2
       (\<lambda>i. qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))))
       [Monitor.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Monitor.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs" 
  proof -
    have "length [Monitor.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Monitor.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] = length zs"
      using buf_and(2)
      unfolding list_all2_iff
      by auto
    moreover have "\<And>i r. (i, r)\<in>set (zip [Monitor.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Monitor.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs) \<Longrightarrow>
        qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) r"
    proof -
      fix i r
      assume "(i, r)\<in>set (zip [Monitor.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Monitor.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs)"
      then have "(i, r)\<in>set (zip [min (Monitor.progress \<sigma> P \<phi> j) (Monitor.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..< min (Monitor.progress \<sigma> P' \<phi> (j + \<delta>)) (Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))] zs)"
        by auto
      then have "\<exists>X V_Y Y.
           qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
           wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
           qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and> r = bin_join n (fv \<phi>) X True V_Y Y"
        using buf_and(2)
        unfolding list_all2_iff
        by fast
      then obtain X V_Y Y where qtables:
        "qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X"
        "qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y"
        "wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
        "r = bin_join n (fv \<phi>) X True V_Y Y"
        by blast

      have "V_Y \<subseteq> fv (formula.Trigger \<alpha> I \<beta>)"
        using qtables(3)
        unfolding wf_dfvs_def
        by (auto split: if_splits)
      then have fvs: "(fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) = fv \<phi> \<union> V_Y"
        using And_Trigger(3)
        by auto

      have "\<And>x. Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> = Formula.sat \<sigma> V (map the x) i \<phi>"
        using sat_the_restrict
        by auto

      have qtable_pos: "(\<And>x.
          wf_tuple n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) x \<Longrightarrow>
          mem_restr R x \<Longrightarrow>
          Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>)))"
      proof (cases "\<forall>j\<le>i. \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)")
        case True
        fix x
        show "Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>))"
          using sat_the_restrict True
          by auto
      next
        case False
        then have V_Y_eq: "V_Y = fv (formula.Trigger \<alpha> I \<beta>)"
          using qtables(3)
          unfolding wf_dfvs_def
          by auto

        fix x
        show "Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>))"
          unfolding V_Y_eq
          using sat_the_restrict
          by auto
      qed

      then show "qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) r"
        unfolding qtables(4)
        using qtable_bin_join[OF qtables(1-2) _ fvs _ qtable_pos, of True]
        by auto
    qed
    ultimately show ?thesis
      unfolding list_all2_iff
      by blast
  qed

  ultimately show ?case using ztuple_eq by auto 
next
  case (And_Release I \<phi>' \<psi>' P v n R aux \<alpha>')
  
  define zs where "zs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db aux)"
  define \<chi> where "\<chi> = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db aux)"

  have ztuple_eq: "(meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db aux) = (zs, \<chi>)"
    using zs_def \<chi>_def
    by auto

  have IH:
    "wf_mformula \<sigma> (j + \<delta>) P' v n R \<chi> (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>')"
    "list_all2 (\<lambda>i. qtable n (fv (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>')) (mem_restr R) (\<lambda>va. Formula.sat \<sigma> v (map the va) i (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>')))
     [Monitor.progress \<sigma> P (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') j..<Monitor.progress \<sigma> P' (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') (j + \<delta>)] zs"
    using And_Release.IH[OF And_Release.prems(1)]
    unfolding ztuple_eq
    by auto
  have "wf_mformula \<sigma> (j + \<delta>) P' v n R \<chi> (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>'))"
    using wf_mformula.And_Release[OF And_Release(1-3) IH(1)]
    by auto
  moreover have "list_all2
       (\<lambda>i. qtable n (fv (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>'))) (mem_restr R) (\<lambda>va. Formula.sat \<sigma> v (map the va) i (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>'))))
       [Monitor.progress \<sigma> P (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')) j..<Monitor.progress \<sigma> P' (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')) (j + \<delta>)] zs"
  proof -
    have "length [Monitor.progress \<sigma> P (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') j..<Monitor.progress \<sigma> P' (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') (j + \<delta>)] = length zs"
      using IH(2)
      unfolding list_all2_iff
      by auto
    
    then have "length [Monitor.progress \<sigma> P (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')) j..<Monitor.progress \<sigma> P' (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')) (j + \<delta>)] =
    length zs"
      by (auto simp only: progress_and_release_rewrite_bounded[OF And_Release(1-2)])
    moreover have "\<And>i r. (i, r) \<in>set (zip [Monitor.progress \<sigma> P (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')) j..<Monitor.progress \<sigma> P' (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')) (j + \<delta>)] zs) \<Longrightarrow>
        qtable n (fv (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>'))) (mem_restr R) (\<lambda>va. Formula.sat \<sigma> v (map the va) i (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>'))) r"
    proof -
      fix i r
      assume "(i, r) \<in>set (zip [Monitor.progress \<sigma> P (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')) j..<Monitor.progress \<sigma> P' (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')) (j + \<delta>)] zs)"
      then have "(i, r) \<in>set (zip [Monitor.progress \<sigma> P (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') j..<Monitor.progress \<sigma> P' (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') (j + \<delta>)] zs)"
        by (auto simp only: progress_and_release_rewrite_bounded[OF And_Release(1-2),symmetric])
      then have qtable: "qtable n (fv (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>')) (mem_restr R) (\<lambda>va. Formula.sat \<sigma> v (map the va) i (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>')) r"
        using IH(2)
        unfolding list_all2_iff
        by auto
      
      show "qtable n (fv (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>'))) (mem_restr R) (\<lambda>va. Formula.sat \<sigma> v (map the va) i (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>'))) r"
        using qtable release_fvi(3) sat_and_release_rewrite[OF And_Release(2,1)]
        unfolding qtable_def
        by (auto intro!: qtableI[of n "(fv (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')))" r "(mem_restr R)" "(\<lambda>va. Formula.sat \<sigma> v (map the va) i (formula.And \<alpha>' (formula.Release \<phi>' I \<psi>')))"])
    qed
    ultimately show ?thesis
      unfolding list_all2_iff
      by blast
  qed
  ultimately show ?case using ztuple_eq by auto
next
  case (Ands P V n R l pos neg l' buf A_pos A_neg)
  note mbufn_take.simps[simp del] mbufn_add.simps[simp del] mmulti_join.simps[simp del]

  from Ands(1) have wf_l: "list_all2 (wf_mformula \<sigma> j P V n R) l (pos @ map remove_neg neg)"
    unfolding list_all2_iff
    by auto

  from Ands have
    wf_buf: "wf_mbufn (progress \<sigma> P (formula.Ands l') j) (map (\<lambda>\<psi>. progress \<sigma> P \<psi> j) (pos @ map remove_neg neg))
      (map (\<lambda>\<psi> i. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>)) (pos @ map remove_neg neg)) buf" and
    posneg: "(pos, neg) = partition safe_formula l'" and
    pos_nonempty: "pos \<noteq> []" and
    safe_neg: "list_all safe_formula (map remove_neg neg)" and
    A_eq: "A_pos = map fv pos" "A_neg = map fv neg" and
    fv_subset: "\<Union> (set A_neg) \<subseteq> \<Union> (set A_pos)"
    by auto
  have progress_eq: "progress \<sigma> P' (formula.Ands l') (j + \<delta>) =
      Mini (progress \<sigma> P (formula.Ands l') j) (map (\<lambda>\<psi>. progress \<sigma> P' \<psi> (j + \<delta>)) (pos @ map remove_neg neg))"
    using \<open>pos \<noteq> []\<close> posneg
    by (auto simp: Mini_def image_Un[symmetric] Collect_disj_eq[symmetric] intro!: arg_cong[where f=Min])

  have join_ok: "qtable n (\<Union> (fv ` set l')) (mem_restr R)
        (\<lambda>v. list_all (Formula.sat \<sigma> V (map the v) k) l')
        (mmulti_join n A_pos A_neg L)"
    if args_ok: "list_all2 (\<lambda>x. qtable n (fv x) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k x))
        (pos @ map remove_neg neg) L"
    for k L
  proof (rule qtable_mmulti_join)
    let ?ok = "\<lambda>A Qi X. qtable n A (mem_restr R) Qi X \<and> wf_set n A"
    let ?L_pos = "take (length A_pos) L"
    let ?L_neg = "drop (length A_pos) L"
    have 1: "length pos \<le> length L"
      using args_ok by (auto dest!: list_all2_lengthD)
    show "list_all3 ?ok A_pos (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k \<psi>) pos) ?L_pos"
      using args_ok wf_l unfolding A_eq
      by (auto simp add: list_all3_conv_all_nth list_all2_conv_all_nth nth_append
          split: if_splits intro!: wf_mformula_wf_set[of \<sigma> j P V n R]
          dest: order.strict_trans2[OF _ 1])
    from args_ok have prems_neg: "list_all2 (\<lambda>\<psi>. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (remove_neg \<psi>))) neg ?L_neg"
      by (auto simp: A_eq list_all2_append1 list.rel_map)
    show "list_all3 ?ok A_neg (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k (remove_neg \<psi>)) neg) ?L_neg"
      using prems_neg wf_l unfolding A_eq
      by (auto simp add: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length nth_append less_diff_conv
          split: if_splits intro!: wf_mformula_wf_set[of \<sigma> j P V n R _ "remove_neg _", simplified])
    show "\<Union>(fv ` set l') = \<Union>(set A_pos)"
      using fv_subset posneg unfolding A_eq by auto
    show "L = take (length A_pos) L @ drop (length A_pos) L" by simp
    show "A_pos \<noteq> []" using \<open>pos \<noteq> []\<close> A_eq by simp

    fix x :: "event_data tuple"
    assume "wf_tuple n (\<Union> (fv ` set l')) x" and "mem_restr R x"
    then show "list_all (\<lambda>A. mem_restr R (restrict A x)) A_pos"
      and "list_all (\<lambda>A. mem_restr R (restrict A x)) A_neg"
      by (simp_all add: list.pred_set)

    have "list_all Formula.is_Neg neg"
      using posneg safe_neg
      by (auto 0 3 simp add: list.pred_map elim!: list.pred_mono_strong
          intro: formula.exhaust[of \<psi> "Formula.is_Neg \<psi>" for \<psi>])
    then have "list_all (\<lambda>\<psi>. Formula.sat \<sigma> V (map the v) i (remove_neg \<psi>) \<longleftrightarrow>
      \<not> Formula.sat \<sigma> V (map the v) i \<psi>) neg" for v i
      by (fastforce simp: Formula.is_Neg_def elim!: list.pred_mono_strong)
    then show "list_all (Formula.sat \<sigma> V (map the x) k) l' =
       (list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos
         (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k \<psi>) pos) \<and>
        list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg
         (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k
                       (remove_neg \<psi>))
           neg))"
      using posneg
      by (auto simp add: A_eq list_all2_conv_all_nth list_all_length sat_the_restrict
          elim: nth_filter nth_partition[where P=safe_formula and Q="Formula.sat _ _ _ _"])
  qed fact

  have "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip l (pos @ map remove_neg neg)) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
    wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>' \<and>
    list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
  proof -
    fix \<phi> \<phi>'
    
    assume "(\<phi>, \<phi>') \<in> set (zip l (pos @ map remove_neg neg))"
    then have "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
            (case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> of
             (xs, \<phi>\<^sub>n) \<Rightarrow>
               wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' \<and>
               list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs)"
      using Ands.IH Ands.prems(1)
      unfolding list_all2_iff[of "(\<lambda>\<phi> \<phi>'.
         wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
         (\<forall>x xa.
             wf_envs \<sigma> j \<delta> P xa V x \<longrightarrow>
             (case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) x \<phi> of
              (xs, \<phi>\<^sub>n) \<Rightarrow>
                wf_mformula \<sigma> (j + \<delta>) xa V n R \<phi>\<^sub>n \<phi>' \<and>
                list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> xa \<phi>' (j + \<delta>)]
                 xs)))" l "(pos @ map remove_neg neg)"]
      by fastforce
    then have
      "wf_mformula \<sigma> j P V n R \<phi> \<phi>'"
      "case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> of
         (xs, \<phi>\<^sub>n) \<Rightarrow>
           wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' \<and>
           list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
      by auto
    then show
      "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
      wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>' \<and>
      list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
      by auto
  qed
  then have IH:
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip l (pos @ map remove_neg neg)) \<Longrightarrow> wf_mformula \<sigma> j P V n R \<phi> \<phi>'"
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip l (pos @ map remove_neg neg)) \<Longrightarrow> wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>'"
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip l (pos @ map remove_neg neg)) \<Longrightarrow> list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
    by auto

  from Ands.prems(1) show ?case
    by (auto 0 3 simp add: list.rel_map progress_eq map2_map_map list_all3_map
        list_all3_list_all2_conv list.pred_map
        simp del: set_append map_append progress_simps split: prod.splits
        intro!: wf_mformula.Ands[OF _ _ posneg \<open>pos \<noteq> []\<close> safe_neg A_eq fv_subset]
        rel_mono_zip[OF wf_l] wf_mbufn_add[OF wf_buf]
        list.rel_flip[THEN iffD1, OF rel_mono_zip, OF wf_l]
        list.rel_refl join_ok[unfolded list.pred_set]
        IH
        elim!: wf_mbufn_take list_all2_appendI
        elim: mbufn_take_induct[OF _ wf_mbufn_add[OF wf_buf]])
next
  case (Or P V n R \<phi> \<phi>' \<psi> \<psi>' buf)
  show ?case using Or(1-4) Or.prems Or.IH[OF Or.prems]
    by (auto  split: if_splits prod.splits intro!: wf_mformula.Or qtable_union
      elim: mbuf2_take_add'(1) list.rel_mono_strong[OF mbuf2_take_add'(2)])
next
  case (Neg P V n R \<phi> \<phi>')
  have *: "qtable n {} (mem_restr R) (\<lambda>v. P v) X \<Longrightarrow>
    \<not> qtable n {} (mem_restr R) (\<lambda>v. \<not> P v) empty_table \<Longrightarrow> x \<in> X \<Longrightarrow> False" for P x X
    using nullary_qtable_cases qtable_unit_empty_table by fastforce
  from Neg show ?case
    by (auto 0 4 intro!: wf_mformula.Neg dest!: Neg.IH
        simp add: list.rel_map
        dest: nullary_qtable_cases qtable_unit_empty_table intro!: qtable_empty_unit_table
        elim!: list.rel_mono_strong elim: *)
next
  case (Exists P V n R \<phi> \<phi>')
  then show ?case
    by (force simp: list.rel_map fvi_Suc sat_fv_cong nth_Cons'
        intro!: wf_mformula.Exists dest!: Exists.IH qtable_project_fv
        elim!: list.rel_mono_strong table_fvi_tl qtable_cong sat_fv_cong[THEN iffD1, rotated -1]
        split: if_splits)+
next
  case (Agg P V b n R \<phi> \<phi>' y f g0 \<omega>)

  define xs where "xs = fst (meval (b+n) (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"
  define \<phi>'' where "\<phi>'' = snd (meval (b+n) (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"

  have xtuple_eq: "meval (b+n) (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (xs, \<phi>'')"
    using xs_def \<phi>''_def
    by auto

  define zs where "zs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAgg g0 y \<omega> b f \<phi>))"
  define \<psi>'' where "\<psi>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAgg g0 y \<omega> b f \<phi>))"

  have ztuple_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MAgg g0 y \<omega> b f \<phi>) = (zs, \<psi>'')"
    using zs_def \<psi>''_def
    by auto 

  have zs_eq: "zs = map (eval_agg n g0 y \<omega> b f) xs"
    unfolding zs_def meval.simps
    by (auto simp add: xtuple_eq)

  have \<psi>''_eq: "\<psi>'' = MAgg g0 y \<omega> b f \<phi>''"
    unfolding \<psi>''_def meval.simps Let_def
    by (auto simp add: xtuple_eq)

  have IH:
    "wf_mformula \<sigma> (j + \<delta>) P' V (b + n) (lift_envs' b R) \<phi>'' \<phi>'"
    "list_all2 (\<lambda>i. qtable (b + n) (fv \<phi>') (mem_restr (lift_envs' b R)) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
     [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
    using Agg.IH[OF Agg.prems]
    by (auto simp add: xtuple_eq)

  have wf: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<psi>'' (formula.Agg y \<omega> b f \<phi>')"
    unfolding \<psi>''_eq
    using wf_mformula.Agg[OF IH(1) Agg(2-6)]
    by auto
  moreover have "list_all2 (\<lambda>i. qtable n (fv (formula.Agg y \<omega> b f \<phi>')) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Agg y \<omega> b f \<phi>')))
       [Monitor.progress \<sigma> P (formula.Agg y \<omega> b f \<phi>') j..<Monitor.progress \<sigma> P' (formula.Agg y \<omega> b f \<phi>') (j + \<delta>)] zs"
  proof -
    have "length [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] = length xs"
      using IH(2)
      unfolding list_all2_iff
      by auto
    moreover have "length xs = length zs"
      using zs_eq
      by auto
    moreover have progress_eq: "[Monitor.progress \<sigma> P (formula.Agg y \<omega> b f \<phi>') j..<Monitor.progress \<sigma> P' (formula.Agg y \<omega> b f \<phi>') (j + \<delta>)] = [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)]"
      by auto
    ultimately have len_eq: "length [Monitor.progress \<sigma> P (formula.Agg y \<omega> b f \<phi>') j..<Monitor.progress \<sigma> P' (formula.Agg y \<omega> b f \<phi>') (j + \<delta>)] = length zs"
      by auto
    moreover have "\<And>i r. (i, r)\<in>set (zip [Monitor.progress \<sigma> P (formula.Agg y \<omega> b f \<phi>') j..<Monitor.progress \<sigma> P' (formula.Agg y \<omega> b f \<phi>') (j + \<delta>)] zs) \<Longrightarrow>
        qtable n (fv (formula.Agg y \<omega> b f \<phi>')) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Agg y \<omega> b f \<phi>')) r"
    proof -
      define zipped where "zipped = zip [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (map (eval_agg n g0 y \<omega> b f) xs)"
      fix i r
      assume assm: "(i, r)\<in>set (zip [Monitor.progress \<sigma> P (formula.Agg y \<omega> b f \<phi>') j..<Monitor.progress \<sigma> P' (formula.Agg y \<omega> b f \<phi>') (j + \<delta>)] zs)"
      then have mem: "(i, r) \<in> set zipped"
        unfolding zs_eq zipped_def
        by (auto simp add: progress_eq)

      have "length zs = length (zip [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] zs)"
        using progress_eq len_eq
        by auto
      obtain idx where idx_props:
        "idx \<in> {0..<length zipped}"
        "(i, r) = zipped!idx"
        using mem
        by (metis atLeastLessThan_iff in_set_conv_nth zero_le)
      have idx_l:
        "idx < length [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] "
        "idx < length (map (eval_agg n g0 y \<omega> b f) xs)"
        using idx_props(1)
        unfolding zipped_def length_zip
        by auto

      define r' where "r' = xs ! idx"

      have nth:
        "i = [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)]!idx"
        "r = (map (eval_agg n g0 y \<omega> b f) xs)!idx"
        using nth_zip[OF idx_l] idx_props(2)
        unfolding zipped_def
        by auto
      then have r_def: "r = eval_agg n g0 y \<omega> b f r'"
        unfolding r'_def
        using nth_map[of "idx" "xs" "(eval_agg n g0 y \<omega> b f)"] idx_l(2)
        by auto

      have "(i, r') = (zip [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs) ! idx"
        using r'_def nth(1) idx_l
        by auto
      then have "(i, r') \<in> set (zip [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs)"
        using idx_l in_set_conv_nth
        by force
      then have qtable: "qtable (b + n) (fv \<phi>') (mem_restr (lift_envs' b R)) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>') r'"
        using IH(2)
        unfolding list_all2_iff
        by auto

      have fvs_l_n: "\<forall>x\<in>fv (formula.Agg y \<omega> b f \<phi>'). x < n"
        using wf_mformula_wf_set[OF wf, unfolded wf_set_def]
        by auto
      
      show "qtable n (fv (formula.Agg y \<omega> b f \<phi>')) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Agg y \<omega> b f \<phi>')) r"
        using qtable_eval_agg[OF qtable fvs_l_n Agg(3-6)] r_def
        by auto
    qed
    ultimately show ?thesis
      unfolding list_all2_iff
      by auto
  qed
  ultimately show ?case
    using ztuple_eq
    by auto
next
  case (Prev P V n R \<phi> \<psi> first buf nts I)
  let ?xs = "fst (meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>)"
  let ?\<phi> = "snd (meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>)"
  let ?ls = "fst (mprev_next I (buf @ ?xs) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]))"
  let ?rs = "fst (snd (mprev_next I (buf @ ?xs) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])))"
  let ?ts = "snd (snd (mprev_next I (buf @ ?xs) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])))"
  let ?P = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) X"
  let ?i = "min (progress \<sigma> P \<psi> j) (j - 1)"
  let ?j = "j + \<delta>"
  let ?j' = "progress \<sigma> P' \<psi> (j + \<delta>)"
  define mini where "mini = min ?j' (if ?i = ?j then ?j else ?j - 1)"
  
  from Prev.IH[OF Prev.prems] have IH: "wf_mformula \<sigma> (j + \<delta>) P' V n R ?\<phi> \<psi>" and
    "list_all2 ?P [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> (j + \<delta>)] ?xs" by auto
  with Prev(3,4) Prev.prems have
    "list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then ?P i X else X = empty_table) [?i..<mini] ?ls \<and>
     list_all2 ?P [mini..<?j'] ?rs \<and> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [mini..< ?j] ?ts"
    unfolding mini_def
    by (intro mprev) (auto intro!: list_all2_upt_append list_all2_appendI order.trans[OF min.cobounded1]
      list.rel_refl simp: list.rel_map)
  moreover have "min (Suc (progress \<sigma> P \<psi> j)) j = Suc (min (progress \<sigma> P \<psi> j) (j-1))" if "j > 0" for P j
    using that by auto
  ultimately show ?case using Prev(2) Prev.prems IH
    upt_conv_Cons[OF zero_less_Suc, of "min (Monitor.progress \<sigma> P' \<psi> \<delta>) (\<delta> - Suc 0)"]
    by (auto 0 3 simp: map_Suc_upt[symmetric] list.rel_map qtable_empty_iff mini_def
        simp del: upt_Suc elim!: wf_mformula.Prev list.rel_mono_strong dest: wf_envs_progress_le
        split: prod.split if_split_asm) (* slow 25 sec*)
next
  case (Next P V n R \<phi> \<psi> first nts I)
  have min[simp]:
    "min (progress \<sigma> P \<psi> j - Suc 0) (j - Suc 0) = progress \<sigma> P \<psi> j - Suc 0"
    "min (progress \<sigma> P' \<psi> (j + \<delta>) - Suc 0) (j + \<delta> - Suc 0) = progress \<sigma> P' \<psi> (j + \<delta>) - Suc 0"
    using wf_envs_progress_le[OF Next.prems(1), of \<psi>] by auto

  let ?xs = "fst (meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>)"
  let ?ys = "case (?xs, first) of (_ # xs, True) \<Rightarrow> xs | _ \<Rightarrow> ?xs"
  let ?\<phi> = "snd (meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>)"
  let ?ls = "fst (mprev_next I ?ys (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]))"
  let ?rs = "fst (snd (mprev_next I ?ys (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])))"
  let ?ts = "snd (snd (mprev_next I ?ys (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])))"
  let ?P = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) X"
  let ?i = "progress \<sigma> P \<psi> j - 1"
  let ?j = "j + \<delta>"
  let ?j' = "progress \<sigma> P' \<psi> (j + \<delta>)"
  define mini where "mini = min (?j' - 1) (if ?i = ?j then ?j else ?j - 1)"
  
  from Next.IH[OF Next.prems(1)] have IH: "wf_mformula \<sigma> (j + \<delta>) P' V  n R ?\<phi> \<psi>"
    "list_all2 ?P [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> (j + \<delta>)] ?xs" by auto
  then have "list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then ?P (Suc i) X else X = empty_table)
       [?i..<mini] ?ls \<and>
     list_all2 ?P [Suc mini..<?j'] ?rs \<and> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [mini..<?j] ?ts"
     if "progress \<sigma> P \<psi> j < progress \<sigma> P' \<psi> (j + \<delta>)"
    using Next(1-3) IH that wf_envs_progress_le[OF Next.prems(1), of \<psi>] unfolding mini_def
    by (intro mnext)
      (auto simp: list_all2_Cons2 upt_eq_Cons_conv list.rel_map
        intro!: list_all2_upt_append list_all2_appendI list.rel_refl split: list.splits)
  then show ?case using wf_envs_progress_le[OF Next.prems(1), of \<psi>]
    upt_add_eq_append[of 0 j \<delta>] upt_add_eq_append[of "?j' - 1" j \<delta>]
    wf_envs_progress_mono[OF Next.prems(1), of j "j + \<delta>" \<psi>, simplified] Next(1-3) IH
    by (cases "progress \<sigma> P' \<psi> (j + \<delta>) > progress \<sigma> P \<psi> j")
      (auto 0 3 simp: qtable_empty_iff le_Suc_eq le_diff_conv mini_def list.rel_map
        elim!: wf_mformula.Next list.rel_mono_strong list_all2_appendI intro!: list.rel_refl
        split: prod.split list.splits if_split_asm) (* slow 15 sec*)
next
  case (Since P V n R \<phi> \<phi>'' \<psi> \<psi>'' args \<phi>''' I buf nts aux)
  note sat.simps[simp del]
  from Since have
       pos: "if args_pos args then \<phi>''' = \<phi>'' else \<phi>''' = Formula.Neg \<phi>''"
    and pos_eq: "safe_formula \<phi>''' = args_pos args"
    and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<psi>''"
    and fvi_subset: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
    and buf: "wf_mbuf2' \<sigma> P V j n R \<phi>'' \<psi>'' buf"
    and nts: "wf_ts \<sigma> P j \<phi>'' \<psi>'' nts"
    and aux: "wf_since_aux \<sigma> V R args \<phi>'' \<psi>'' aux (progress \<sigma> P (Formula.Since \<phi>''' I \<psi>'') j)"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>''"
    and args_R: "args_R args = Formula.fv \<psi>''"
    by auto
  have \<phi>''': "Formula.fv \<phi>''' = Formula.fv \<phi>''" "progress \<sigma> P \<phi>''' j = progress \<sigma> P \<phi>'' j"
    "progress \<sigma> P' \<phi>''' j = progress \<sigma> P' \<phi>'' j" for j
    using pos by (simp_all split: if_splits)
  from Since.prems(1) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  have update: "wf_since_aux \<sigma> V R args \<phi>'' \<psi>'' (snd (zs, aux')) (progress \<sigma> P' (Formula.Since \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
    list_all2 (\<lambda>i. qtable n (Formula.fv \<phi>''' \<union> Formula.fv \<psi>'') (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Since \<phi>''' I \<psi>'')))
      [progress \<sigma> P (Formula.Since \<phi>''' I \<psi>'') j..<progress \<sigma> P' (Formula.Since \<phi>''' I \<psi>'') (j + \<delta>)] (fst (zs, aux'))"
    if eval_\<phi>: "fst (meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>) = xs"
      and eval_\<psi>: "fst (meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<psi>) = ys"
      and eq: "mbuf2t_take (\<lambda>r1 r2 t (zs, aux).
        case update_since args r1 r2 t aux of (z, x) \<Rightarrow> (zs @ [z], x))
        ([], aux) (mbuf2_add xs ys buf) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) = ((zs, aux'), buf', nts')"
    for xs ys zs aux' buf' nts'
    unfolding progress_simps \<phi>'''
  proof (rule mbuf2t_take_add_induct'[where j=j and j'="j + \<delta>" and z'="(zs, aux')",
      OF eq wf_envs_P_simps[OF Since.prems(1)] buf nts_snoc],
      goal_cases xs ys _ base step)
    case xs
    then show ?case
      using Since.IH(1)[OF Since.prems(1)] eval_\<phi> by auto
  next
    case ys
    then show ?case
      using Since.IH(2)[OF Since.prems(1)] eval_\<psi> by auto
  next
    case base
    then show ?case
      using aux by (simp add: \<phi>''')
  next
    case (step k X Y z)
    then show ?case
      using fvi_subset pos
      by (auto 0 3 simp: args_ivl args_n args_L args_R Un_absorb1
          elim!: update_since(1) list_all2_appendI dest!: update_since(2)
          split: prod.split if_splits)
  qed simp
  with Since.IH(1)[OF Since.prems(1)] Since.IH(2)[OF Since.prems(1)] show ?case
    by (auto 0 3 split: prod.split
        intro: wf_mformula.Since[OF _ _ pos pos_eq args_ivl args_n args_L args_R fvi_subset]
        elim: mbuf2t_take_add'(1)[OF _ wf_envs_P_simps[OF Since.prems(1)] buf nts_snoc]
              mbuf2t_take_add'(2)[OF _ wf_envs_P_simps[OF Since.prems(1)] buf nts_snoc])
next
  case (Until P V n R \<phi> \<phi>'' \<psi> \<psi>'' args \<phi>''' I buf nts t aux)
  note sat.simps[simp del] progress_simps[simp del]
  from Until have
        pos: "if args_pos args then \<phi>''' = \<phi>'' else \<phi>''' = Formula.Neg \<phi>''"
    and pos_eq: "safe_formula \<phi>''' = args_pos args"
    and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<psi>''"
    and fvi_subset: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
    and buf: "wf_mbuf2' \<sigma> P V j n R \<phi>'' \<psi>'' buf"
    and nts: "wf_ts \<sigma> P j \<phi>'' \<psi>'' nts"
    and aux: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>''"
    and args_R: "args_R args = Formula.fv \<psi>''"
    and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))))"
    and length_aux: "progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j + length_muaux args aux =
      min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)"
    by auto
  define pos where args_pos: "pos = args_pos args"
  have \<phi>''': "progress \<sigma> P \<phi>''' j = progress \<sigma> P \<phi>'' j"  "progress \<sigma> P' \<phi>''' j = progress \<sigma> P' \<phi>'' j" for j
    using pos by (simp_all add: progress.simps split: if_splits)
  from Until.prems(1) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  {
    fix xs ys zs aux' aux'' buf' nts' nt
    assume eval_\<phi>: "fst (meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>) = xs"
      and eval_\<psi>: "fst (meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<psi>) = ys"
      and nt0: "nt = lookahead_ts nts' nts (map (\<tau> \<sigma>) [j ..< j + \<delta>]) t"
      and eq1: "mbuf2t_take (add_new_muaux args) aux (mbuf2_add xs ys buf) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) =
        (aux', buf', nts')"
      and eq2: "eval_muaux args nt aux' = (zs, aux'')"
    define ne where "ne \<equiv> progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j"
    have update1: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux' (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j) \<and>
      ne + length_muaux args aux' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
      using Until.IH(1)[OF Until.prems(1)] eval_\<phi> Until.IH(2)[OF Until.prems(1)]
        eval_\<psi> nts_snoc nts_snoc length_aux aux fvi_subset
      unfolding \<phi>'''
      by (elim mbuf2t_take_add_induct'[where j'="j + \<delta>", OF eq1 wf_envs_P_simps[OF Until.prems(1)] buf])
        (auto simp: args_n args_L args_R ne_def wf_update_until)
    then obtain cur auxlist' where valid_aux': "valid_muaux args cur aux' auxlist'" and
      cur: "cur = (if ne + length auxlist' = 0 then 0 else \<tau> \<sigma> (ne + length auxlist' - 1))" and
      wf_auxlist': "wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
      unfolding wf_until_aux_def ne_def args_ivl args_n args_pos by auto
    have length_aux': "length_muaux args aux' = length auxlist'"
      using valid_length_muaux[OF valid_aux'] .
    have nts': "wf_ts \<sigma> P' (j + \<delta>) \<phi>'' \<psi>'' nts'"
      using Until.IH(1)[OF Until.prems(1)] eval_\<phi> Until.IH(2)[OF Until.prems(1)]
        Until.prems(1) eval_\<psi> nts_snoc
      unfolding wf_ts_def
      by (intro mbuf2t_take_eqD(2)[OF eq1]) (auto intro: wf_mbuf2_add buf[unfolded wf_mbuf2'_def])
    have nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
      using nts nts' unfolding nt0 t
      apply (auto simp: hd_append hd_rev last_map wf_ts_def lookahead_ts_def)
      using list_all2_hdD(1) list_all2_hdD(2) apply fastforce
      using list_all2_lastD  apply fastforce
        apply (metis (mono_tags) list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
       apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
      apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
      done
    define zs'' where "zs'' = fst (eval_until I nt auxlist')"
    define auxlist'' where "auxlist'' = snd (eval_until I nt auxlist')"
    have current_w_le: "cur \<le> nt"
    proof (cases nts')
      case Nil
      have p_le: "min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<le> j + \<delta>"
        using wf_envs_progress_le[OF Until.prems(1)]
        by (auto simp: min_def le_diff_conv)
      then show ?thesis
        unfolding cur conjunct2[OF update1, unfolded length_aux'] nt
        using Nil by (auto simp: \<phi>''' intro!: \<tau>_mono)
    next
      case (Cons nt x)
      have progress_\<phi>''': "progress \<sigma> P' \<phi>'' (j + \<delta>) = progress \<sigma> P' \<phi>''' (j + \<delta>)"
        using pos by (auto simp add: progress.simps split: if_splits)
      have p_le: "min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<le> j + \<delta>"
        using wf_envs_progress_le[OF Until.prems(1)]
        by (auto simp: min_def le_diff_conv)
      then show ?thesis
        unfolding cur conjunct2[OF update1, unfolded length_aux'] Cons progress_\<phi>''' nt
        by (auto split: if_splits list.splits intro!: \<tau>_mono)
    qed
    have valid_aux'': "valid_muaux args cur aux'' auxlist''"
      using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'' auxlist'']
      by (auto simp add: args_ivl zs''_def auxlist''_def)
    have length_aux'': "length_muaux args aux'' = length auxlist''"
      using valid_length_muaux[OF valid_aux''] .
    have eq2': "eval_until I nt auxlist' = (zs, auxlist'')"
      using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'' auxlist'']
      by (auto simp add: args_ivl zs''_def auxlist''_def)
    have length_aux'_aux'': "length_muaux args aux' = length zs + length_muaux args aux''"
      using eval_until_length[OF eq2'] unfolding length_aux' length_aux'' .
    have "i \<le> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<Longrightarrow>
      wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' i \<Longrightarrow>
      i + length auxlist' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<Longrightarrow>
      wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist'' (progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
        i + length zs = progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
        i + length zs + length auxlist'' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
        list_all2 (\<lambda>i. qtable n (Formula.fv \<psi>'') (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Until (if pos then \<phi>'' else Formula.Neg \<phi>'') I \<psi>'')))
          [i..<i + length zs] zs" for i
      using eq2'
    proof (induction auxlist' arbitrary: zs auxlist'' i)
      case Nil
      then show ?case
        by (auto dest!: antisym[OF progress_Until_le])
    next
      case (Cons a aux')
      obtain t a1 a2 where "a = (t, a1, a2)" by (cases a)
      from Cons.prems(2) have aux': "wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux' (Suc i)"
        by (rule wf_until_aux_Cons)
      from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
        unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons1)
      from Cons.prems(2) have 3: "qtable n (Formula.fv \<psi>'') (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Formula.sat \<sigma> V (map the v) j \<psi>'' \<and>
        (\<forall>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (map the v) k \<phi>'' else \<not> Formula.sat \<sigma> V (map the v) k \<phi>''))) a2"
        unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons3)
      from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' =
          min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
        by simp
      have "i \<ge> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
        if "memR I (nt - t)"
        using that nts' unfolding wf_ts_def progress.simps nt
        by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv \<phi>'''
          intro!: cInf_lower \<tau>_mono diff_le_mono simp del: upt_Suc split: if_splits list.splits)
      moreover
      have "Suc i \<le> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
        if "\<not> memR I (nt - t)"
      proof -
        have \<tau>_min:  "\<tau> \<sigma> (min (j + \<delta> - 1) k) = min (\<tau> \<sigma> (j + \<delta> - 1)) (\<tau> \<sigma> k)" for k
          by (simp add: min_of_mono monoI)
        have le_progress_iff[simp]: "j + \<delta> \<le> progress \<sigma> P' \<phi> (j + \<delta>) \<longleftrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) = (j + \<delta>)" for \<phi>
          using wf_envs_progress_le[OF Until.prems(1), of \<phi>] by auto
        let ?X = "{i. \<forall>k. k < j + \<delta> \<and> k \<le> min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
        let ?min = "min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))"
        have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> (j + \<delta>)"
          by (rule \<tau>_mono) auto
        from that have "?X \<noteq> {}"
          by (auto simp: \<phi>''' intro!: exI[of _ "progress \<sigma> P' \<phi>'' (j + \<delta>)"])
        show ?thesis
          using that nts' Suc_i_aux' unfolding wf_ts_def progress.simps nt
          by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
            (auto 0 3 simp: 1 \<phi>''' list_all2_Cons2 upt_eq_Cons_conv
              simp del: upt_Suc split: list.splits if_splits
              dest!: spec[of _ "?min"]
              intro: diff_le_mono diff_le_mono2 order_trans[OF diff_le_mono diff_le_mono2] \<tau>_mono
              elim!: contrapos_np[of _ "Suc i \<le> _"])
      qed
      moreover have *: "k < progress \<sigma> P' \<psi> (j + \<delta>)" if
        "\<not> memR I (nt - \<tau> \<sigma> i)"
        "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "\<psi> = \<psi>'' \<or> \<psi> = \<phi>''" for k \<psi>
        using that nts' unfolding wf_ts_def nt
        by (auto simp: list_all2_Cons2 upt_eq_Cons_conv
          simp del: upt_Suc split: list.splits if_splits
          elim!: contrapos_np[of _ "k < _"] intro!: diff_le_mono diff_le_mono2)
      ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
        unfolding \<open>a = (t, a1, a2)\<close>
        by (auto simp: \<phi>''' 1 sat.simps upt_conv_Cons dest!: Cons.IH[OF _ aux' Suc_i_aux']
            simp del: upt_Suc split: if_splits prod.splits intro!: iff_exI qtable_cong[OF 3 refl])
    qed
    note wf_aux'' = this[OF wf_envs_progress_mono[OF Until.prems(1) le_add1]
      wf_auxlist' conjunct2[OF update1, unfolded ne_def length_aux']]
    have "progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length auxlist' =
      progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist''"
      using wf_aux'' valid_aux'' length_aux'_aux''
      by (auto simp add: ne_def length_aux' length_aux'')
    then have "cur =
      (if progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist'' = 0 then 0
      else \<tau> \<sigma> (progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist'' - 1))"
      unfolding cur ne_def by auto
    then have "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux'' (progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
      progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs = progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
      progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs + length_muaux args aux'' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
      list_all2 (\<lambda>i. qtable n (fv \<psi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Until (if pos then \<phi>'' else formula.Neg \<phi>'') I \<psi>'')))
      [progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs] zs \<and>
      nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
      using wf_aux'' valid_aux'' fvi_subset
      unfolding wf_until_aux_def length_aux'' args_ivl args_n args_pos nt by (auto simp only: length_aux'')
  }
  note update = this[OF refl refl refl, rotated]
  from Until.IH(1)[OF Until.prems(1)] Until.IH(2)[OF Until.prems(1)] pos pos_eq fvi_subset show ?case
    unfolding meval.simps Let_def
    by (auto simp: args_ivl args_n args_pos \<phi>''' progress.simps(6) Let_def
        split: prod.split if_splits dest!: update
        intro!: wf_mformula.Until[OF _ _ _ _ args_ivl args_n args_L args_R fvi_subset]
        elim!: list.rel_mono_strong qtable_cong
        elim: mbuf2t_take_add'(1)[OF _ wf_envs_P_simps[OF Until.prems(1)] buf nts_snoc]
        mbuf2t_take_add'(2)[OF _ wf_envs_P_simps[OF Until.prems(1)] buf nts_snoc])
next
  case (Trigger_0 P V n R \<psi> \<beta> args \<alpha> \<gamma> \<phi> I buf nts aux)

  from Trigger_0 have
        pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = formula.Neg \<gamma>"
    and pos_eq: "safe_formula \<alpha> = args_pos args"
    and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<gamma>"
    and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<beta>"
    and fvi_subset: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>"
    and buf: "wf_mbuf2' \<sigma> P V j n R \<gamma> \<beta> buf"
    and nts: "wf_ts \<sigma> P j \<gamma> \<beta> nts"
    and aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux (Monitor.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = fv \<gamma>"
    and args_R: "args_R args = fv \<beta>"
    and fv_l_n: "\<forall>x\<in>fv \<beta>. x < n"
    and mem0: "mem I 0"
    by auto

  have args_props:
    "args_n args = n"
    "args_R args = fv \<alpha> \<union> fv \<beta>"
    "fv \<gamma> = fv \<alpha>"
    using pos args_n args_L args_R fvi_subset
    by (auto split: if_splits)

  note IH_\<phi> = Trigger_0.IH(2)[OF Trigger_0.prems(1)]
  note IH_\<psi> = Trigger_0.IH(1)[OF Trigger_0.prems(1)]

  define zs where "zs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MTrigger args \<phi> \<psi> buf nts aux))"
  define \<eta> where "\<eta> = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MTrigger args \<phi> \<psi> buf nts aux))"

  define xs where "xs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"
  define \<gamma>' where "\<gamma>' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"

  have \<phi>_pair_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (xs, \<gamma>')"
    unfolding xs_def \<gamma>'_def
    by auto

  have \<gamma>_props:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<gamma>' \<gamma>"
    "list_all2 (\<lambda>i. qtable n (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>)) [Monitor.progress \<sigma> P \<gamma> j..<Monitor.progress \<sigma> P' \<gamma> (j + \<delta>)] xs"
    using IH_\<phi>
    unfolding \<phi>_pair_eq
    by auto

  define ys where "ys = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi>)"
  define \<beta>' where "\<beta>' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi>)"

  have \<psi>_pair_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> = (ys, \<beta>')"
    unfolding ys_def \<beta>'_def
    by auto

  have \<beta>_props:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<beta>' \<beta>"
    "list_all2 (\<lambda>i. qtable n (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>)) [Monitor.progress \<sigma> P \<beta> j..<Monitor.progress \<sigma> P' \<beta> (j + \<delta>)] ys"
    using IH_\<psi>
    unfolding \<psi>_pair_eq
    by auto

  define tuple where "tuple = mbuf2t_take (\<lambda>r1 r2 t (zs, aux). let
    aux = update_mtaux args t r1 r2 aux;
    (fv_z, z) = result_mtaux args aux
    in
      (zs @ [z], aux)
  ) ([], aux) (mbuf2_add xs ys buf) (nts @ map (\<tau> \<sigma>) [j..<j + \<delta>])"

  have zs_eq: "zs = fst (fst tuple)"
    unfolding tuple_def zs_def meval.simps Let_def xs_def ys_def
    by (auto split: prod.splits)

  define aux' where "aux' = snd (fst tuple)"
  define buf' where "buf' = fst (snd tuple)"
  define nts' where "nts' = snd (snd tuple)"

  have tuple_eq: "tuple = ((zs, aux'), buf', nts')"
    unfolding zs_eq aux'_def buf'_def nts'_def Let_def
    by auto

  have \<eta>_eq: "\<eta> = MTrigger args \<gamma>' \<beta>' buf' nts' aux'"
    unfolding \<eta>_def meval.simps \<gamma>'_def \<beta>'_def aux'_def buf'_def nts'_def tuple_def xs_def ys_def Let_def
    by (auto split: prod.splits)

  have pred_mapping:
    "pred_mapping (\<lambda>i. i \<le> j) P"
    "pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
    "rel_mapping (\<le>) P P'"
    using Trigger_0.prems(1)
    by auto

  from Trigger_0.prems(1) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<gamma> j) (progress \<sigma> P \<beta> j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts
    unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)

  have wf_buf_ts:
    "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R \<gamma> \<beta> buf'"
    "wf_ts \<sigma> P' (j + \<delta>) \<gamma> \<beta> nts'"
    using mbuf2t_take_add'[OF tuple_eq[unfolded tuple_def] pred_mapping buf nts_snoc \<gamma>_props(2) \<beta>_props(2)]
    by auto

  have \<alpha>_\<gamma>_props: "Formula.fv \<alpha> = Formula.fv \<gamma>" "progress \<sigma> P \<alpha> j = progress \<sigma> P \<gamma> j"
  "progress \<sigma> P' \<alpha> j = progress \<sigma> P' \<gamma> j" for j
    using pos
    by (simp_all split: if_splits)

  have update: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (zs, aux')) (Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)) \<and>
  list_all2 (\<lambda>i. qtable n (Formula.fv \<alpha> \<union> Formula.fv \<beta>) (mem_restr R)
    (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
    [progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)] (fst (zs, aux'))"
  unfolding progress_simps \<alpha>_\<gamma>_props
  proof (rule mbuf2t_take_add_induct'[where j=j and j'="j + \<delta>" and z'="(zs, aux')",
      OF tuple_eq[unfolded tuple_def] wf_envs_P_simps[OF Trigger_0.prems(1)] buf nts_snoc],
      goal_cases xs ys _ base step)
    case xs
    then show ?case using \<gamma>_props(2) by auto
  next
    case ys
    then show ?case using \<beta>_props(2) by auto
  next
    case base
    then show ?case
      using aux \<alpha>_\<gamma>_props
      unfolding progress_simps 
      by auto
  next
    case (step k X Y acc)
    define zs where "zs = fst acc"
    define aux where "aux = snd acc"
    have z_eq: "acc = (zs, aux)"
      unfolding zs_def aux_def
      by auto

    have table:
      "table (args_n args) (args_L args) X"
      "table (args_n args) (args_R args) Y"
      using step(4-5) args_n args_L args_R
      unfolding qtable_def
      by auto

    define zs' where "zs' = fst (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux))"
    define aux' where "aux' = snd (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux))"
    define cur' where "cur' = \<tau> \<sigma> k"

    have wf_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux k"
      using step(6)
      unfolding aux_def
      by auto
    then have fv_subset: "fv \<gamma> \<subseteq> fv \<beta> "
      unfolding wf_trigger_aux_def
      by auto

    have wf_trigger_aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
      using update_trigger[OF wf_trigger step(4-5) args_n args_L args_R]
      by auto

    then obtain auxlist' where
      valid_mtaux: "valid_mtaux args (\<tau> \<sigma> k) (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')" and
      sorted_wrt: "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'" and
      auxlist_len: "length auxlist' = Suc k" and
      auxlist_props: "(\<forall>(i, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist').
         Suc k \<noteq> 0 \<and>
         t = \<tau> \<sigma> i \<and>
         t \<le> \<tau> \<sigma> k \<and>
         qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
         qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
      )" and
      auxlist_mem: "(\<forall>i.
          Suc k \<noteq> 0 \<and>
          i \<le> k
          \<longrightarrow>
          (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
      )"
      unfolding wf_trigger_aux_def
      by auto

    then have sorted: "sorted (map fst auxlist')"
      using sorted_wrt
      by (simp add: sorted_map)
    have "\<exists>X. (\<tau> \<sigma> k, X) \<in> set auxlist'"
      using auxlist_mem auxlist_len
      by (metis Zero_not_Suc less_Suc_eq_le nth_mem order_refl)
    then obtain X_tmp where "(\<tau> \<sigma> k, X_tmp) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
      using args_ivl mem0
      by auto
    then have non_empty: "(length (filter (\<lambda> (t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist') > 0)"
      using length_pos_if_in_set[of "(\<tau> \<sigma> k, X_tmp)"]
      by auto
    
    have "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux)))
 (Suc k)"
      using wf_trigger_aux
      unfolding z_eq Let_def
      by (auto split: prod.splits)
    moreover have "list_all2
    (\<lambda>i. qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
    [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k]
    (fst (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux)))"
    proof -
      have aux'_eq: "aux' = update_mtaux args (\<tau> \<sigma> k) X Y aux"
        unfolding aux'_def Let_def
        by (auto split: prod.splits)
      define fv_z where "fv_z = fst (result_mtaux args aux')"
      define z where "z = snd (result_mtaux args aux')"
      define auxlist'' where "auxlist'' = (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"

      have valid_mtaux': "valid_mtaux args (\<tau> \<sigma> k) aux' auxlist''"
        unfolding aux'_eq auxlist''_def
        using valid_mtaux
        by auto
      have z_eq: "z = snd (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have equiv: "(x \<in> z) =
         Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)" if
          restr: "mem_restr R x" and
          wf_x: "wf_tuple (args_n args) (args_R args) x"
        for x
        unfolding z_eq auxlist''_def
        using trigger_sat_equiv[OF restr wf_x pos args_n args_ivl args_L args_R fvi_subset fv_l_n valid_mtaux sorted_wrt auxlist_len auxlist_props auxlist_mem non_empty]
        by auto

      have filter_inv: "(filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') = (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist')"
        unfolding auxlist''_def filter_filter
        by (metis (mono_tags, lifting) case_prod_beta')

      have "result_mtaux args aux' = trigger_results args cur' auxlist''"
        using valid_result_mtaux[OF valid_mtaux]
        unfolding aux'_def cur'_def auxlist''_def
        by auto
      moreover have "(length (filter (\<lambda> (t, _). mem (args_ivl args) (cur' - t)) auxlist'') > 0)"
        using filter_inv non_empty
        unfolding cur'_def auxlist''_def
        by auto
      ultimately have z_eq': "z = {
        tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
          (\<forall>i \<in> {0..<(length auxlist'')}.
            let (t, l, r) = auxlist''!i in
            mem (args_ivl args) (cur' - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist'')}.
                join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
              )
            )
          )
        }"
        unfolding z_def
        by auto

      have args_R_simp: "args_R args = fv \<alpha> \<union> fv \<beta>"
        using args_L args_R pos fvi_subset
        by (auto split: if_splits)
      have table: "table n (fv \<alpha> \<union> fv \<beta>) z"
        using z_eq'
        unfolding table_def args_R_simp args_n
        by auto

      have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
        using equiv args_props
        by auto

      have completeness: "\<And>x. wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
        using equiv args_props
        by auto

      have qtable_k: "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
        using qtableI[OF table correctness completeness]
        by auto

      have zs'_eq: "zs' = zs @ [z]"
        unfolding zs'_def z_def aux'_eq  Let_def
        by (auto split: prod.splits)

      have IH: "list_all2
        (\<lambda>i. qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
        [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs"
        using step(6) zs_def args_props(3)
        by auto
      then have "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] = length zs"
        unfolding list_all2_iff
        by auto
      then have len: "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
        unfolding zs'_eq length_append
        by (simp add: step(1))

      moreover have "(\<forall>(i, r) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] zs').
      qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
      proof -
        {
          fix i r
          assume assm: "(i, r) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k] zs')"
          
          have "length [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] = length zs"
            using step(6) zs_def
            unfolding list_all2_iff
            by auto
          moreover have "[min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] @ [k] =
                         [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k]"
            by (simp add: step(1))
          ultimately have zip_eq:
            "zip ([min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
             zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [z]"
            unfolding zs'_eq
            using zip_append[of "[min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[z]"]
            by auto
          {
            assume "(i, r) \<in> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs)"
            then have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              using step(6) args_props(3) zs_def
              unfolding list_all2_iff
              by auto
          }
          moreover {
            assume "(i, r) \<notin> set (zip [min (Monitor.progress \<sigma> P \<gamma> j) (Monitor.progress \<sigma> P \<beta> j)..<k] zs)"
            then have "(i, r) = (k, z)"
              using assm zip_eq
              by auto
            then have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              using qtable_k
              by auto
          }
          ultimately have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
            by blast
        }
        then show ?thesis by auto
      qed

      ultimately show ?thesis
        unfolding list_all2_iff zs'_def zs_def aux_def
        by (auto split: prod.splits)
    qed

    ultimately show ?case using args_props(3) by auto
  qed (auto)

  have aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux' (Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))"
    using update
    by auto

  have "wf_mformula \<sigma> (j + \<delta>) P' V n R \<eta> (formula.Trigger \<alpha> I \<beta>)"
    unfolding \<eta>_eq
    using wf_mformula.Trigger_0[OF \<beta>_props(1) pos \<gamma>_props(1) pos_eq args_ivl args_n args_L args_R fv_l_n fvi_subset wf_buf_ts aux mem0]
    by auto

  moreover have "list_all2 (\<lambda>i. qtable n (fv (formula.Trigger \<alpha> I \<beta>)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>))) [Monitor.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<Monitor.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)] zs"
    using update
    by auto

  ultimately show ?case
    unfolding zs_def \<eta>_def
    by auto
next
  case (Release_0 I \<phi>' \<psi>' P V n R aux)

  define xs where "xs = fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db aux)"
  define \<phi>'' where "\<phi>'' = snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db aux)"

  have tuple_eq: "meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db aux = (xs, \<phi>'')"
    using xs_def \<phi>''_def
    by auto

  have IH:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>'' (release_safe_0 \<phi>' I \<psi>')"
    "list_all2 (\<lambda>i. qtable n (fv (release_safe_0 \<phi>' I \<psi>')) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (release_safe_0 \<phi>' I \<psi>')))
     [Monitor.progress \<sigma> P (release_safe_0 \<phi>' I \<psi>') j..<Monitor.progress \<sigma> P' (release_safe_0 \<phi>' I \<psi>') (j + \<delta>)] xs"
    using Release_0.IH[OF Release_0.prems(1)]
    by (auto simp add: tuple_eq)

  have "list_all2 (\<lambda>i. qtable n (fv (release_safe_0 \<phi>' I \<psi>')) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Release \<phi>' I \<psi>')))
    [Monitor.progress \<sigma> P (formula.Release \<phi>' I \<psi>') j..<Monitor.progress \<sigma> P' (formula.Release \<phi>' I \<psi>') (j + \<delta>)] xs"
    using IH(2)
    unfolding sat_release_rewrite_0[OF Release_0(1-2), symmetric] progress_release_rewrite_0[OF Release_0(1)]
    by auto
  moreover have "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>'' (formula.Release \<phi>' I \<psi>')"
    using wf_mformula.Release_0[OF Release_0(1-3) IH(1)]
    by auto

  ultimately show ?case
    using tuple_eq release_fvi(1)
    by (auto)
next
  case (MatchP r P V n R \<phi>s mr mrs buf nts I aux) (* (Formula.MatchP I r) *)
  note sat.simps[simp del] mbufnt_take.simps[simp del] mbufn_add.simps[simp del]
  from MatchP obtain \<psi>s where
        safe: "safe_regex Past Strict r"
    and mr: "to_mregex r = (mr, \<psi>s)"
    and mrs: "mrs = sorted_list_of_set (RPDs mr)"
    and \<psi>s: "list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<psi>s"
    and buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and nts: "wf_ts_regex \<sigma> P j r nts"
    and aux: "wf_matchP_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchP I r) j)"
    using list_all2_mono
    by fastforce

  have IH_alt: "list_all2
     (\<lambda>x1 x2.
         wf_mformula \<sigma> j P V n R x1 x2 \<and>
         (\<forall>x xa.
             wf_envs \<sigma> j \<delta> P xa V x \<longrightarrow>
             (case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) x x1 of
              (xs, \<phi>\<^sub>n) \<Rightarrow>
                wf_mformula \<sigma> (j + \<delta>) xa V n R \<phi>\<^sub>n x2 \<and>
                list_all2 (\<lambda>i. qtable n (fv x2) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i x2)) [Monitor.progress \<sigma> P x2 j..<Monitor.progress \<sigma> xa x2 (j + \<delta>)]
                 xs)))
     \<phi>s \<psi>s"
    using MatchP.IH mr
    by auto

  have "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
    wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>' \<and>
    list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
  proof -
    fix \<phi> \<phi>'
    
    assume "(\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s)"
    then have "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
            (case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> of
             (xs, \<phi>\<^sub>n) \<Rightarrow>
               wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' \<and>
               list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs)"
      using IH_alt MatchP.prems(1)
      unfolding list_all2_iff[of "(\<lambda>x1 x2.
           wf_mformula \<sigma> j P V n R x1 x2 \<and>
           (\<forall>x xa.
               wf_envs \<sigma> j \<delta> P xa V x \<longrightarrow>
               (case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) x x1 of
                (xs, \<phi>\<^sub>n) \<Rightarrow>
                  wf_mformula \<sigma> (j + \<delta>) xa V n R \<phi>\<^sub>n x2 \<and>
                  list_all2 (\<lambda>i. qtable n (fv x2) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i x2)) [Monitor.progress \<sigma> P x2 j..<Monitor.progress \<sigma> xa x2 (j + \<delta>)]
                   xs)))" \<phi>s \<psi>s]
      by fastforce
    then have
      "wf_mformula \<sigma> j P V n R \<phi> \<phi>'"
      "case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> of
         (xs, \<phi>\<^sub>n) \<Rightarrow>
           wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' \<and>
           list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
      by auto
    then show
      "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
      wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>' \<and>
      list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
      by auto
  qed
  then have IH:
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s) \<Longrightarrow> wf_mformula \<sigma> j P V n R \<phi> \<phi>'"
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s) \<Longrightarrow> wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>'"
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s) \<Longrightarrow> list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
    by auto

  have wf_mformula_map: "list_all2 (wf_mformula \<sigma> (j + \<delta>) P' V n R) (map (snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db) \<phi>s) \<psi>s"
  proof -
    have len_eq: "length \<phi>s = length \<psi>s"
      using IH_alt
      unfolding list_all2_iff
      by auto
    then have "length (map (snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db) \<phi>s) = length \<psi>s"
      by auto
    moreover have "\<And>\<phi> \<phi>'. (\<phi>, \<phi>')\<in>set (zip (map (snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db) \<phi>s) \<psi>s) \<Longrightarrow> wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi> \<phi>'"
    proof -
      define f where "f = snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db"
      fix \<phi> \<phi>'
      assume "(\<phi>, \<phi>')\<in>set (zip (map (snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db) \<phi>s) \<psi>s)"
      then have "(\<phi>, \<phi>')\<in>set (zip (map f \<phi>s) \<psi>s)"
        unfolding f_def
        by auto
      then obtain \<phi>'' where \<phi>''_props:
        "(\<phi>'', \<phi>')\<in>set (zip \<phi>s \<psi>s)"
        "\<phi> = f \<phi>''"
        by (metis len_eq fst_conv in_set_zip nth_map snd_conv)
      then have "wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>'')) \<phi>'"
        using IH(2)
        by auto
      then show "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi> \<phi>'"
        using \<phi>''_props(2)
        unfolding f_def
        by auto
    qed
    ultimately show ?thesis
      unfolding list_all2_iff
      by auto
  qed

  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_regex_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_regex_le[OF MatchP.prems(1)] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  have update: "wf_matchP_aux \<sigma> V n R I r (snd (zs, aux')) (progress \<sigma> P' (Formula.MatchP I r) (j + \<delta>)) \<and>
    list_all2 (\<lambda>i. qtable n (Formula.fv_regex r) (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.MatchP I r)))
      [progress \<sigma> P (Formula.MatchP I r) j..<progress \<sigma> P' (Formula.MatchP I r) (j + \<delta>)] (fst (zs, aux'))"
    if eval: "map (fst o meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db) \<phi>s = xss"
      and eq: "mbufnt_take (\<lambda>rels t (zs, aux).
        case update_matchP n I mr mrs rels t aux of (z, x) \<Rightarrow> (zs @ [z], x))
        ([], aux) (mbufn_add xss buf) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) = ((zs, aux'), buf', nts')"
    for xss zs aux' buf' nts'
    unfolding progress_simps
  proof (rule mbufnt_take_add_induct'[where j'="j + \<delta>" and z'="(zs, aux')", OF eq wf_envs_P_simps[OF MatchP.prems(1)] safe mr buf nts_snoc],
      goal_cases xss _ base step)
    case xss
    then show ?case
      using eval \<psi>s
      by (auto simp: list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map
          list.rel_flip[symmetric, of _ \<psi>s \<phi>s] dest!: IH
          elim!: rel_mono_zip split: prod.splits)
  next
    case base
    then show ?case
      using aux by auto
  next
    case (step k Xs z)
    then show ?case
      by (auto simp: Un_absorb1 mrs safe mr elim!: update_matchP(1) list_all2_appendI
          dest!: update_matchP(2) split: prod.split)
  qed simp
  
  then show ?case using \<psi>s wf_mformula_map
    by (auto simp: mr mrs safe map_split_alt list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
        list_all3_map map2_map_map list_all3_list_all2_conv  intro!: wf_mformula.intros
        elim!: rel_mono_zip mbufnt_take_add'(1)[OF _ wf_envs_P_simps[OF MatchP.prems(1)] safe mr buf nts_snoc]
        mbufnt_take_add'(2)[OF _ wf_envs_P_simps[OF MatchP.prems(1)] safe mr buf nts_snoc]
        dest!: IH split: prod.splits)
next
  case (MatchF r P V n R \<phi>s mr mrs buf nts t I aux)
  note sat.simps[simp del] mbufnt_take.simps[simp del] mbufn_add.simps[simp del] progress_simps[simp del]
  from MatchF obtain \<psi>s where
        safe: "safe_regex Futu Strict r"
    and mr: "to_mregex r = (mr, \<psi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and \<psi>s: "list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<psi>s"
    and buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and nts: "wf_ts_regex \<sigma> P j r nts"
    and aux: "wf_matchF_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchF I r) j) 0"
    and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (progress_regex \<sigma> P r j)))"
    and length_aux: "progress \<sigma> P (Formula.MatchF I r) j + length aux = progress_regex \<sigma> P r j"
    using list_all2_mono
    by fastforce
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [progress_regex \<sigma> P r j..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_regex_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_regex_le[OF MatchF.prems(1)] list.rel_map
      intro!: list_all2_appendI list.rel_refl)

  have IH_alt: "list_all2
     (\<lambda>x1 x2.
         wf_mformula \<sigma> j P V n R x1 x2 \<and>
         (\<forall>x xa.
             wf_envs \<sigma> j \<delta> P xa V x \<longrightarrow>
             (case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) x x1 of
              (xs, \<phi>\<^sub>n) \<Rightarrow>
                wf_mformula \<sigma> (j + \<delta>) xa V n R \<phi>\<^sub>n x2 \<and>
                list_all2 (\<lambda>i. qtable n (fv x2) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i x2)) [Monitor.progress \<sigma> P x2 j..<Monitor.progress \<sigma> xa x2 (j + \<delta>)]
                 xs)))
     \<phi>s \<psi>s"
    using MatchF.IH mr
    by auto

  have "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s) \<Longrightarrow>
    wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
    wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>' \<and>
    list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
  proof -
    fix \<phi> \<phi>'
    
    assume "(\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s)"
    then have "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
            (case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> of
             (xs, \<phi>\<^sub>n) \<Rightarrow>
               wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' \<and>
               list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs)"
      using IH_alt MatchF.prems(1)
      unfolding list_all2_iff[of "(\<lambda>x1 x2.
           wf_mformula \<sigma> j P V n R x1 x2 \<and>
           (\<forall>x xa.
               wf_envs \<sigma> j \<delta> P xa V x \<longrightarrow>
               (case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) x x1 of
                (xs, \<phi>\<^sub>n) \<Rightarrow>
                  wf_mformula \<sigma> (j + \<delta>) xa V n R \<phi>\<^sub>n x2 \<and>
                  list_all2 (\<lambda>i. qtable n (fv x2) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i x2)) [Monitor.progress \<sigma> P x2 j..<Monitor.progress \<sigma> xa x2 (j + \<delta>)]
                   xs)))" \<phi>s \<psi>s]
      by fastforce
    then have
      "wf_mformula \<sigma> j P V n R \<phi> \<phi>'"
      "case meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> of
         (xs, \<phi>\<^sub>n) \<Rightarrow>
           wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' \<and>
           list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
      by auto
    then show
      "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<and>
      wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>' \<and>
      list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
      by auto
  qed
  then have IH:
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s) \<Longrightarrow> wf_mformula \<sigma> j P V n R \<phi> \<phi>'"
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s) \<Longrightarrow> wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)) \<phi>'"
    "\<And>\<phi> \<phi>'. (\<phi>, \<phi>') \<in> set (zip \<phi>s \<psi>s) \<Longrightarrow> list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')) [Monitor.progress \<sigma> P \<phi>' j..<Monitor.progress \<sigma> P' \<phi>' (j + \<delta>)] (fst (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>))"
    by auto

  have wf_mformula_map: "list_all2 (wf_mformula \<sigma> (j + \<delta>) P' V n R) (map (snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db) \<phi>s) \<psi>s"
  proof -
    have len_eq: "length \<phi>s = length \<psi>s"
      using IH_alt
      unfolding list_all2_iff
      by auto
    then have "length (map (snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db) \<phi>s) = length \<psi>s"
      by auto
    moreover have "\<And>\<phi> \<phi>'. (\<phi>, \<phi>')\<in>set (zip (map (snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db) \<phi>s) \<psi>s) \<Longrightarrow> wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi> \<phi>'"
    proof -
      define f where "f = snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db"
      fix \<phi> \<phi>'
      assume "(\<phi>, \<phi>')\<in>set (zip (map (snd \<circ> meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db) \<phi>s) \<psi>s)"
      then have "(\<phi>, \<phi>')\<in>set (zip (map f \<phi>s) \<psi>s)"
        unfolding f_def
        by auto
      then obtain \<phi>'' where \<phi>''_props:
        "(\<phi>'', \<phi>')\<in>set (zip \<phi>s \<psi>s)"
        "\<phi> = f \<phi>''"
        by (metis len_eq fst_conv in_set_zip nth_map snd_conv)
      then have "wf_mformula \<sigma> (j + \<delta>) P' V n R (snd (meval n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>'')) \<phi>'"
        using IH(2)
        by auto
      then show "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi> \<phi>'"
        using \<phi>''_props(2)
        unfolding f_def
        by auto
    qed
    ultimately show ?thesis
      unfolding list_all2_iff
      by auto
  qed

  {
    fix xss zs aux' aux'' buf' nts' nt
    assume eval: "map (fst o meval n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db) \<phi>s = xss"
      and nt0: "nt = lookahead_ts nts' nts (map (\<tau> \<sigma>) [j ..< j + \<delta>]) t"
      and eq1: "mbufnt_take (update_matchF n I mr mrs) aux (mbufn_add xss buf) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) =
        (aux', buf', nts')"
      and eq2: "eval_matchF I mr nt aux' = (zs, aux'')"
    have update1: "wf_matchF_aux \<sigma> V n R I r aux' (progress \<sigma> P (Formula.MatchF I r) j) 0 \<and>
      progress \<sigma> P (Formula.MatchF I r) j + length aux' = progress_regex \<sigma> P' r (j + \<delta>)"
      using eval nts_snoc nts_snoc length_aux aux \<psi>s
      by (elim mbufnt_take_add_induct'[where j'="j + \<delta>", OF eq1 wf_envs_P_simps[OF MatchF.prems(1)] safe mr buf])
        (auto simp: length_update_matchF
          list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
          dest!: IH
          elim: wf_update_matchF[OF _ safe mr mrs] elim!: rel_mono_zip)
    from MatchF.prems(1) have nts': "wf_ts_regex \<sigma> P' (j + \<delta>) r nts'"
      using eval eval nts_snoc \<psi>s
      unfolding wf_ts_regex_def
      apply (intro mbufnt_take_eqD(2)[OF eq1 wf_mbufn_add[where js'="map (\<lambda>\<phi>. progress \<sigma> P' \<phi> (j + \<delta>)) \<psi>s",
              OF buf[unfolded wf_mbufn'_def mr prod.case]]])
      apply (auto simp: to_mregex_progress[OF safe mr] Mini_def
          list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
          list_all2_Cons1 elim!: rel_mono_zip intro!: list.rel_refl_strong
          dest!: IH)
      apply (auto simp: list_all2_conv_all_nth)
      done
    have nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (progress_regex \<sigma> P' r (j + \<delta>))))"
      using nts nts' unfolding nt0 t
      apply (auto simp: hd_append hd_rev last_map wf_ts_regex_def lookahead_ts_def)
      using list_all2_hdD(1) list_all2_hdD(2) apply fastforce
      using list_all2_lastD apply fastforce
        apply (metis (mono_tags) list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
       apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
      apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
      done
    have "i \<le> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>) \<Longrightarrow>
      wf_matchF_aux \<sigma> V n R I r aux' i 0 \<Longrightarrow>
      i + length aux' = progress_regex \<sigma> P' r (j + \<delta>) \<Longrightarrow>
      wf_matchF_aux \<sigma> V n R I r aux'' (progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)) 0 \<and>
        i + length zs = progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>) \<and>
        i + length zs + length aux'' = progress_regex \<sigma> P' r (j + \<delta>) \<and>
        list_all2 (\<lambda>i. qtable n (Formula.fv_regex r) (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.MatchF I r)))
          [i..<i + length zs] zs" for i
      using eq2
    proof (induction aux' arbitrary: zs aux'' i)
      case Nil
      then show ?case by (auto dest!: antisym[OF progress_MatchF_le])
    next
      case (Cons a aux')
      obtain t rels rel where "a = (t, rels, rel)" by (cases a)
      from Cons.prems(2) have aux': "wf_matchF_aux \<sigma> V n R I r aux' (Suc i) 0"
        by (rule wf_matchF_aux_Cons)
      from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
        unfolding \<open>a = (t, rels, rel)\<close> by (rule wf_matchF_aux_Cons1)
      from Cons.prems(2) have 3: "qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Regex.match (Formula.sat \<sigma> V (map the v)) r i j)) rel"
        unfolding \<open>a = (t, rels, rel)\<close> using wf_matchF_aux_Cons3 by force
      from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' = progress_regex \<sigma> P' r (j + \<delta>)"
        by simp
      have "i \<ge> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)"
        if "memR I (nt - t)"
        using that nts' unfolding wf_ts_regex_def progress_simps nt
        by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv
          intro!: cInf_lower \<tau>_mono diff_le_mono simp del: upt_Suc split: if_splits list.splits)
      moreover
      have "Suc i \<le> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)"
        if "\<not> memR I (nt - t)"
      proof -
        have \<tau>_min:  "\<tau> \<sigma> (min (j + \<delta> - 1) k) = min (\<tau> \<sigma> (j + \<delta> - 1) ) (\<tau> \<sigma> k)" for k
          by (simp add: min_of_mono monoI)
        have le_progress_iff[simp]: "j + \<delta> \<le> progress \<sigma> P' \<phi> (j + \<delta>) \<longleftrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) = (j + \<delta>)" for \<phi>
          using wf_envs_progress_le[OF MatchF.prems(1), of \<phi>] by auto
        have min_Suc[simp]: "min j (j + \<delta>) = j" by auto
        let ?X = "{i. \<forall>k. k < j + \<delta> \<and> k \<le> progress_regex \<sigma> P' r (j + \<delta>) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
        let ?min = "min (j + \<delta> - 1) (progress_regex \<sigma> P' r (j + \<delta>))"
        have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> (j + \<delta>)"
          by (rule \<tau>_mono) auto
        from that have "?X \<noteq> {}"
          by (auto intro!: exI[of _ "progress_regex \<sigma> P' r (j + \<delta>)"])
        show ?thesis
          using that nts' wf_envs_progress_regex_le[OF MatchF.prems(1), of r]
          unfolding wf_ts_regex_def progress_simps nt
          by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
            (auto 0 3 simp: 1 list_all2_Cons2 upt_eq_Cons_conv
              simp del: upt_Suc split: list.splits if_splits
              dest!: spec[of _ "?min"]
              intro!: diff_le_mono diff_le_mono2 order_trans[OF diff_le_mono diff_le_mono2] \<tau>_mono
              elim!: contrapos_np[of _ "Suc i \<le> _"])
      qed
      moreover have *: "k < progress_regex \<sigma> P' r (j + \<delta>)" if
        "\<not> memR I (nt - \<tau> \<sigma> i)"
        "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
        using that nts' unfolding wf_ts_regex_def nt
        by (auto simp: list_all2_Cons2 upt_eq_Cons_conv
          simp del: upt_Suc split: list.splits if_splits
          elim!: contrapos_np[of _ "k < _"] intro!: diff_le_mono diff_le_mono2)
      ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
        unfolding \<open>a = (t, rels, rel)\<close>
        by (auto simp: 1 sat.simps upt_conv_Cons dest!: Cons.IH[OF _ aux' Suc_i_aux']
            simp del: upt_Suc split: if_splits prod.splits intro!: iff_exI qtable_cong[OF 3 refl])

    qed
    note conjI[OF nt this[OF progress_mono_gen[OF le_add1] conjunct1[OF update1] conjunct2[OF update1]]]
  }
  note update = this[OF refl refl, rotated]
  from MatchF.prems(1) show ?case using \<psi>s wf_mformula_map
    by (auto simp: mr mrs safe map_split_alt list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
        list_all3_map map2_map_map list_all3_list_all2_conv Let_def
        intro!: wf_mformula.intros
        elim!: rel_mono_zip mbufnt_take_add'(1)[OF _ wf_envs_P_simps[OF MatchF.prems(1)] safe mr buf nts_snoc]
        mbufnt_take_add'(2)[OF _ wf_envs_P_simps[OF MatchF.prems(1)] safe mr buf nts_snoc]
        dest!: IH update split: prod.splits)
qed

subsubsection \<open>Monitor step\<close>

lemma (in maux) wf_mstate_mstep: "wf_mstate \<phi> \<pi> R st \<Longrightarrow> last_ts \<pi> \<le> snd tdb \<Longrightarrow>
  wf_mstate \<phi> (psnoc \<pi> tdb) R (snd (mstep (map_prod mk_db id tdb) st))"
  unfolding wf_mstate_def mstep_def Let_def
  by (fastforce simp add: progress_mono le_imp_diff_is_add split: prod.splits
      elim!: prefix_of_psnocE dest: meval[OF _ wf_envs_mk_db] list_all2_lengthD)

definition "flatten_verdicts Vs = (\<Union> (set (map (\<lambda>(i, X). (\<lambda>v. (i, v)) ` X) Vs)))"

lemma flatten_verdicts_append[simp]:
  "flatten_verdicts (Vs @ Us) = flatten_verdicts Vs \<union> flatten_verdicts Us"
  by (induct Vs) (auto simp: flatten_verdicts_def)

lemma (in maux) mstep_output_iff:
  assumes "wf_mstate \<phi> \<pi> R st" "last_ts \<pi> \<le> snd tdb" "prefix_of (psnoc \<pi> tdb) \<sigma>" "mem_restr R v"
  shows "(i, v) \<in> flatten_verdicts (fst (mstep (map_prod mk_db id tdb) st)) \<longleftrightarrow>
    progress \<sigma> Map.empty \<phi> (plen \<pi>) \<le> i \<and> i < progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>)) \<and>
    wf_tuple (Formula.nfv \<phi>) (Formula.fv \<phi>) v \<and> Formula.sat \<sigma> Map.empty (map the v) i \<phi>"
proof -
  from prefix_of_psnocE[OF assms(3,2)] have "prefix_of \<pi> \<sigma>"
    "\<Gamma> \<sigma> (plen \<pi>) = fst tdb" "\<tau> \<sigma> (plen \<pi>) = snd tdb" by auto
  moreover from assms(1) \<open>prefix_of \<pi> \<sigma>\<close> have "mstate_n st = Formula.nfv \<phi>"
    "mstate_i st = progress \<sigma> Map.empty \<phi> (plen \<pi>)" "wf_mformula \<sigma> (plen \<pi>) Map.empty Map.empty (mstate_n st) R (mstate_m st) \<phi>"
    unfolding wf_mstate_def by blast+
  moreover from meval[OF \<open>wf_mformula \<sigma> (plen \<pi>) Map.empty Map.empty (mstate_n st) R (mstate_m st) \<phi>\<close> wf_envs_mk_db] obtain Vs st' where
    "meval (mstate_n st) [\<tau> \<sigma> (plen \<pi>)] (mk_db (\<Gamma> \<sigma> (plen \<pi>))) (mstate_m st) = (Vs, st')"
    "wf_mformula \<sigma> (Suc (plen \<pi>)) Map.empty Map.empty (mstate_n st) R st' \<phi>"
    "list_all2 (\<lambda>i. qtable (mstate_n st) (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> Map.empty (map the v) i \<phi>))
      [progress \<sigma> Map.empty \<phi> (plen \<pi>)..<progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>))] Vs" by auto
  moreover from this assms(4) have "qtable (mstate_n st) (fv \<phi>) (mem_restr R)
    (\<lambda>v. Formula.sat \<sigma> Map.empty (map the v) i \<phi>) (Vs ! (i - progress \<sigma> Map.empty \<phi> (plen \<pi>)))"
    if "progress \<sigma> Map.empty \<phi> (plen \<pi>) \<le> i" "i < progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>))"
    using that by (auto simp: list_all2_conv_all_nth
        dest!: spec[of _ "(i - progress \<sigma> Map.empty \<phi> (plen \<pi>))"])
  ultimately show ?thesis
    using assms(4) unfolding mstep_def Let_def flatten_verdicts_def
    by (auto simp: in_set_enumerate_eq list_all2_conv_all_nth progress_mono le_imp_diff_is_add
        elim!: in_qtableE in_qtableI intro!: bexI[of _ "(i, Vs ! (i - progress \<sigma> Map.empty \<phi> (plen \<pi>)))"])
qed


subsubsection \<open>Monitor function\<close>

locale verimon = verimon_spec + maux

lemma (in verimon) mstep_mverdicts:
  assumes wf: "wf_mstate \<phi> \<pi> R st"
    and le[simp]: "last_ts \<pi> \<le> snd tdb"
    and restrict: "mem_restr R v"
  shows "(i, v) \<in> flatten_verdicts (fst (mstep (map_prod mk_db id tdb) st)) \<longleftrightarrow>
    (i, v) \<in> M (psnoc \<pi> tdb) - M \<pi>"
proof -
  obtain \<sigma> where p2: "prefix_of (psnoc \<pi> tdb) \<sigma>"
    using ex_prefix_of by blast
  with le have p1: "prefix_of \<pi> \<sigma>" by (blast elim!: prefix_of_psnocE)
  show ?thesis
    unfolding M_def
    by (auto 0 3 simp: p2 progress_prefix_conv[OF _ p1] sat_prefix_conv[OF _ p1] not_less
        pprogress_eq[OF p1] pprogress_eq[OF p2]
        dest: mstep_output_iff[OF wf le p2 restrict, THEN iffD1] spec[of _ \<sigma>]
        mstep_output_iff[OF wf le _ restrict, THEN iffD1] progress_sat_cong[OF p1]
        intro: mstep_output_iff[OF wf le p2 restrict, THEN iffD2] p1)
qed

context maux
begin

primrec msteps0 where
  "msteps0 [] st = ([], st)"
| "msteps0 (tdb # \<pi>) st =
    (let (V', st') = mstep (map_prod mk_db id tdb) st; (V'', st'') = msteps0 \<pi> st' in (V' @ V'', st''))"

primrec msteps0_stateless where
  "msteps0_stateless [] st = []"
| "msteps0_stateless (tdb # \<pi>) st = (let (V', st') = mstep (map_prod mk_db id tdb) st in V' @ msteps0_stateless \<pi> st')"

lemma msteps0_msteps0_stateless: "fst (msteps0 w st) = msteps0_stateless w st"
  by (induct w arbitrary: st) (auto simp: split_beta)

lift_definition msteps :: "Formula.prefix \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate \<Rightarrow> (nat \<times> event_data table) list \<times> ('msaux, 'muaux, 'mtaux) mstate"
  is msteps0 .

lift_definition msteps_stateless :: "Formula.prefix \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate \<Rightarrow> (nat \<times> event_data table) list"
  is msteps0_stateless .

lemma msteps_msteps_stateless: "fst (msteps w st) = msteps_stateless w st"
  by transfer (rule msteps0_msteps0_stateless)

lemma msteps0_snoc: "msteps0 (\<pi> @ [tdb]) st =
   (let (V', st') = msteps0 \<pi> st; (V'', st'') = mstep (map_prod mk_db id tdb) st' in (V' @ V'', st''))"
  by (induct \<pi> arbitrary: st) (auto split: prod.splits)

lemma msteps_psnoc: "last_ts \<pi> \<le> snd tdb \<Longrightarrow> msteps (psnoc \<pi> tdb) st =
   (let (V', st') = msteps \<pi> st; (V'', st'') = mstep (map_prod mk_db id tdb) st' in (V' @ V'', st''))"
  by transfer' (auto simp: msteps0_snoc split: list.splits prod.splits if_splits)

definition monitor where
  "monitor \<phi> \<pi> = msteps_stateless \<pi> (minit_safe \<phi>)"

end

lemma Suc_length_conv_snoc: "(Suc n = length xs) = (\<exists>y ys. xs = ys @ [y] \<and> length ys = n)"
  by (cases xs rule: rev_cases) auto

lemma (in verimon) wf_mstate_msteps: "wf_mstate \<phi> \<pi> R st \<Longrightarrow> mem_restr R v \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow>
  X = msteps (pdrop (plen \<pi>) \<pi>') st \<Longrightarrow> wf_mstate \<phi> \<pi>' R (snd X) \<and>
  ((i, v) \<in> flatten_verdicts (fst X)) = ((i, v) \<in> M \<pi>' - M \<pi>)"
proof (induct "plen \<pi>' - plen \<pi>" arbitrary: X st \<pi> \<pi>')
  case 0
  from 0(1,4,5) have "\<pi> = \<pi>'"  "X = ([], st)"
    by (transfer; auto)+
  with 0(2) show ?case unfolding flatten_verdicts_def by simp
next
  case (Suc x)
  from Suc(2,5) obtain \<pi>'' tdb where "x = plen \<pi>'' - plen \<pi>"  "\<pi> \<le> \<pi>''"
    "\<pi>' = psnoc \<pi>'' tdb" "pdrop (plen \<pi>) (psnoc \<pi>'' tdb) = psnoc (pdrop (plen \<pi>) \<pi>'') tdb"
    "last_ts (pdrop (plen \<pi>) \<pi>'') \<le> snd tdb" "last_ts \<pi>'' \<le> snd tdb"
    "\<pi>'' \<le> psnoc \<pi>'' tdb"
  proof (atomize_elim, transfer, elim exE, goal_cases prefix)
    case (prefix _ _ \<pi>' _ \<pi>_tdb)
    then show ?case
    proof (cases \<pi>_tdb rule: rev_cases)
      case (snoc \<pi> tdb)
      with prefix show ?thesis
        by (intro bexI[of _ "\<pi>' @ \<pi>"] exI[of _ tdb])
          (force simp: sorted_append append_eq_Cons_conv split: list.splits if_splits)+
    qed simp
  qed
  with Suc(1)[OF this(1) Suc.prems(1,2) this(2) refl] Suc.prems show ?case
    unfolding msteps_msteps_stateless[symmetric]
    by (auto simp: msteps_psnoc split_beta mstep_mverdicts
        dest: mono_monitor[THEN set_mp, rotated] intro!: wf_mstate_mstep)
qed

lemma (in verimon) wf_mstate_msteps_stateless:
  assumes "wf_mstate \<phi> \<pi> R st" "mem_restr R v" "\<pi> \<le> \<pi>'"
  shows "(i, v) \<in> flatten_verdicts (msteps_stateless (pdrop (plen \<pi>) \<pi>') st) \<longleftrightarrow> (i, v) \<in> M \<pi>' - M \<pi>"
  using wf_mstate_msteps[OF assms refl] unfolding msteps_msteps_stateless by simp

lemma (in verimon) wf_mstate_msteps_stateless_UNIV: "wf_mstate \<phi> \<pi> UNIV st \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow>
  flatten_verdicts (msteps_stateless (pdrop (plen \<pi>) \<pi>') st) = M \<pi>' - M \<pi>"
  by (auto dest: wf_mstate_msteps_stateless[OF _ mem_restr_UNIV])

lemma (in verimon) mverdicts_Nil: "M pnil = {}"
  by (simp add: M_def pprogress_eq)

context maux
begin

lemma minit_safe_minit: "mmonitorable \<phi> \<Longrightarrow> minit_safe \<phi> = minit \<phi>"
  unfolding minit_safe_def monitorable_formula_code by simp

lemma wf_mstate_minit_safe: "mmonitorable \<phi> \<Longrightarrow> wf_mstate \<phi> pnil R (minit_safe \<phi>)"
  using wf_mstate_minit minit_safe_minit mmonitorable_def by metis

end

lemma (in verimon) monitor_mverdicts: "flatten_verdicts (monitor \<phi> \<pi>) = M \<pi>"
  unfolding monitor_def using monitorable
  by (subst wf_mstate_msteps_stateless_UNIV[OF wf_mstate_minit_safe, simplified])
    (auto simp: mmonitorable_def mverdicts_Nil)

subsection \<open>Collected correctness results\<close>

context verimon
begin

text \<open>We summarize the main results proved above.
\begin{enumerate}
\item The term @{term M} describes semantically the monitor's expected behaviour:
\begin{itemize}
\item @{thm[source] mono_monitor}: @{thm mono_monitor[no_vars]}
\item @{thm[source] sound_monitor}: @{thm sound_monitor[no_vars]}
\item @{thm[source] complete_monitor}: @{thm complete_monitor[no_vars]}
\item @{thm[source] sliceable_M}: @{thm sliceable_M[no_vars]}
\end{itemize}
\item The executable monitor's online interface @{term minit_safe} and @{term mstep}
  preserves the invariant @{term wf_mstate} and produces the the verdicts according
  to @{term M}:
\begin{itemize}
\item @{thm[source] wf_mstate_minit_safe}: @{thm wf_mstate_minit_safe[no_vars]}
\item @{thm[source] wf_mstate_mstep}: @{thm wf_mstate_mstep[no_vars]}
\item @{thm[source] mstep_mverdicts}: @{thm mstep_mverdicts[no_vars]}
\end{itemize}
\item The executable monitor's offline interface @{term monitor} implements @{term M}:
\begin{itemize}
\item @{thm[source] monitor_mverdicts}: @{thm monitor_mverdicts[no_vars]}
\end{itemize}
\end{enumerate}
\<close>

end

(*<*)
end
(*>*)
