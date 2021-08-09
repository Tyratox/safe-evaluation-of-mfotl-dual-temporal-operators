(*<*)
theory Optimized_MTL
  imports Monitor
begin
(*>*)

section \<open>Efficient implementation of temporal operators\<close>

subsection \<open>Optimized queue data structure\<close>

lemma less_enat_iff: "a < enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j < i)"
  by (cases a) auto

type_synonym 'a queue_t = "'a list \<times> 'a list"

definition queue_invariant :: "'a queue_t \<Rightarrow> bool" where
  "queue_invariant q = (case q of ([], []) \<Rightarrow> True | (fs, l # ls) \<Rightarrow> True | _ \<Rightarrow> False)"

typedef 'a queue = "{q :: 'a queue_t. queue_invariant q}"
  by (auto simp: queue_invariant_def split: list.splits)

setup_lifting type_definition_queue

lift_definition linearize :: "'a queue \<Rightarrow> 'a list" is "(\<lambda>q. case q of (fs, ls) \<Rightarrow> fs @ rev ls)" .

lift_definition empty_queue :: "'a queue" is "([], [])"
  by (auto simp: queue_invariant_def split: list.splits)

lemma empty_queue_rep: "linearize empty_queue = []"
  by transfer (simp add: empty_queue_def linearize_def)

lift_definition is_empty :: "'a queue \<Rightarrow> bool" is "\<lambda>q. (case q of ([], []) \<Rightarrow> True | _ \<Rightarrow> False)" .

lemma linearize_t_Nil: "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = [] \<longleftrightarrow> q = ([], [])"
  by (auto split: prod.splits)

lemma is_empty_alt: "is_empty q \<longleftrightarrow> linearize q = []"
  by transfer (auto simp: linearize_t_Nil list.case_eq_if)

fun prepend_queue_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "prepend_queue_t a ([], []) = ([], [a])"
| "prepend_queue_t a (fs, l # ls) = (a # fs, l # ls)"
| "prepend_queue_t a (f # fs, []) = undefined"

lift_definition prepend_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is prepend_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim: prepend_queue_t.elims)

lemma prepend_queue_rep: "linearize (prepend_queue a q) = a # linearize q"
  by transfer
    (auto simp add: queue_invariant_def linearize_def elim: prepend_queue_t.elims split: prod.splits)

lift_definition append_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is
  "(\<lambda>a q. case q of (fs, ls) \<Rightarrow> (fs, a # ls))"
  by (auto simp: queue_invariant_def split: list.splits)

lemma append_queue_rep: "linearize (append_queue a q) = linearize q @ [a]"
  by transfer (auto simp add: linearize_def split: prod.splits)

fun safe_last_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_last_t ([], []) = (None, ([], []))"
| "safe_last_t (fs, l # ls) = (Some l, (fs, l # ls))"
| "safe_last_t (f # fs, []) = undefined"

lift_definition safe_last :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_last_t
  by (auto simp: queue_invariant_def split: prod.splits list.splits)

lemma safe_last_rep: "safe_last q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = last (linearize q))"
  by transfer (auto simp: queue_invariant_def split: list.splits elim: safe_last_t.elims)

fun safe_hd_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_hd_t ([], []) = (None, ([], []))"
| "safe_hd_t ([], [l]) = (Some l, ([], [l]))"
| "safe_hd_t ([], l # ls) = (let fs = rev ls in (Some (hd fs), (fs, [l])))"
| "safe_hd_t (f # fs, l # ls) = (Some f, (f # fs, l # ls))"
| "safe_hd_t (f # fs, []) = undefined"

lift_definition(code_dt) safe_hd :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_hd_t
proof -
  fix q :: "'a queue_t"
  assume "queue_invariant q"
  then show "pred_prod \<top> queue_invariant (safe_hd_t q)"
    by (cases q rule: safe_hd_t.cases) (auto simp: queue_invariant_def Let_def split: list.split)
qed

lemma safe_hd_rep: "safe_hd q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = hd (linearize q))"
  by transfer
    (auto simp add: queue_invariant_def Let_def hd_append split: list.splits elim: safe_hd_t.elims)

fun replace_hd_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "replace_hd_t a ([], []) = ([], [])"
| "replace_hd_t a ([], [l]) = ([], [a])"
| "replace_hd_t a ([], l # ls) = (let fs = rev ls in (a # tl fs, [l]))"
| "replace_hd_t a (f # fs, l # ls) = (a # fs, l # ls)"
| "replace_hd_t a (f # fs, []) = undefined"

lift_definition replace_hd :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is replace_hd_t
  by (auto simp: queue_invariant_def split: list.splits elim: replace_hd_t.elims)

lemma tl_append: "xs \<noteq> [] \<Longrightarrow> tl xs @ ys = tl (xs @ ys)"
  by simp

lemma replace_hd_rep: "linearize q = f # fs \<Longrightarrow> linearize (replace_hd a q) = a # fs"
proof (transfer fixing: f fs a)
  fix q
  assume "queue_invariant q" and "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = f # fs"
  then show "(case replace_hd_t a q of (fs, ls) \<Rightarrow> fs @ rev ls) = a # fs"
    by (cases "(a, q)" rule: replace_hd_t.cases) (auto simp: queue_invariant_def tl_append)
qed

fun replace_last_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "replace_last_t a ([], []) = ([], [])"
| "replace_last_t a (fs, l # ls) = (fs, a # ls)"
| "replace_last_t a (fs, []) = undefined"

lift_definition replace_last :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is replace_last_t
  by (auto simp: queue_invariant_def split: list.splits elim: replace_last_t.elims)

lemma replace_last_rep: "linearize q = fs @ [f] \<Longrightarrow> linearize (replace_last a q) = fs @ [a]"
  by transfer (auto simp: queue_invariant_def split: list.splits prod.splits elim!: replace_last_t.elims)

fun tl_queue_t :: "'a queue_t \<Rightarrow> 'a queue_t" where
  "tl_queue_t ([], []) = ([], [])"
| "tl_queue_t ([], [l]) = ([], [])"
| "tl_queue_t ([], l # ls) = (tl (rev ls), [l])"
| "tl_queue_t (a # as, fs) = (as, fs)"

lift_definition tl_queue :: "'a queue \<Rightarrow> 'a queue" is tl_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim!: tl_queue_t.elims)

lemma tl_queue_rep: "\<not>is_empty q \<Longrightarrow> linearize (tl_queue q) = tl (linearize q)"
  by transfer (auto simp: tl_append split: prod.splits list.splits elim!: tl_queue_t.elims)

lemma length_tl_queue_rep: "\<not>is_empty q \<Longrightarrow>
  length (linearize (tl_queue q)) < length (linearize q)"
  by transfer (auto split: prod.splits list.splits elim: tl_queue_t.elims)

lemma length_tl_queue_safe_hd:
  assumes "safe_hd q = (Some a, q')"
  shows "length (linearize (tl_queue q')) < length (linearize q)"
  using safe_hd_rep[OF assms]
  by (auto simp add: length_tl_queue_rep is_empty_alt)

function dropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "dropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a then dropWhile_queue f (tl_queue q') else q')"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma dropWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  dropWhile P xs = (if P (hd xs) then dropWhile P (tl xs) else xs)"
  by (cases xs) auto

lemma dropWhile_queue_rep: "linearize (dropWhile_queue f q) = dropWhile f (linearize q)"
  by (induction f q rule: dropWhile_queue.induct)
     (auto simp add: tl_queue_rep dropWhile_hd_tl is_empty_alt
      split: prod.splits option.splits dest: safe_hd_rep)

function takeWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "takeWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a
    then prepend_queue a (takeWhile_queue f (tl_queue q'))
    else empty_queue)"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takeWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  takeWhile P xs = (if P (hd xs) then hd xs # takeWhile P (tl xs) else [])"
  by (cases xs) auto

lemma takeWhile_queue_rep: "linearize (takeWhile_queue f q) = takeWhile f (linearize q)"
  by (induction f q rule: takeWhile_queue.induct)
     (auto simp add: prepend_queue_rep tl_queue_rep empty_queue_rep takeWhile_hd_tl is_empty_alt
      split: prod.splits option.splits dest: safe_hd_rep)

function takedropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue \<times> 'a list" where
  "takedropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', [])
  | (Some a, q') \<Rightarrow> if f a
    then (case takedropWhile_queue f (tl_queue q') of (q'', as) \<Rightarrow> (q'', a # as))
    else (q', []))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takedropWhile_queue_fst: "fst (takedropWhile_queue f q) = dropWhile_queue f q"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits) (auto simp add: case_prod_unfold split: option.splits)
qed

lemma takedropWhile_queue_snd: "snd (takedropWhile_queue f q) = takeWhile f (linearize q)"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits)
      (auto simp add: case_prod_unfold tl_queue_rep takeWhile_hd_tl is_empty_alt
        split: option.splits dest: safe_hd_rep)
qed

subsection \<open>Optimized data structure for Since\<close>

type_synonym 'a mmsaux = "ts \<times> ts \<times> bool list \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times>
  (('a tuple, ts) mapping) \<times> (('a tuple, ts) mapping)"

fun time_mmsaux :: "'a mmsaux \<Rightarrow> ts" where
  "time_mmsaux aux = (case aux of (nt, _) \<Rightarrow> nt)"

definition ts_tuple_rel_f :: "('b \<Rightarrow> 'a table) \<Rightarrow> (ts \<times> 'b) set \<Rightarrow> (ts \<times> 'a tuple) set" where
  "ts_tuple_rel_f f ys = {(t, as). \<exists>X. as \<in> (f X) \<and> (t, X) \<in> ys}"

abbreviation "ts_tuple_rel ys \<equiv> ts_tuple_rel_f id ys"

lemma finite_fst_ts_tuple_rel: "finite (fst ` {tas \<in> ts_tuple_rel_f f (set xs). P tas})"
proof -
  have "fst ` {tas \<in> ts_tuple_rel_f f (set xs). P tas} \<subseteq> fst ` ts_tuple_rel_f f (set xs)"
    by auto
  moreover have "\<dots> \<subseteq> set (map fst xs)"
    by (force simp add: ts_tuple_rel_f_def)
  finally show ?thesis
    using finite_subset by blast
qed

lemma ts_tuple_rel_ext_Cons: "tas \<in> ts_tuple_rel_f f {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_ext_Cons': "tas \<in> ts_tuple_rel_f f (set tass) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_intro: "as \<in> f X \<Longrightarrow> (t, X) \<in> ys \<Longrightarrow> (t, as) \<in> ts_tuple_rel_f f ys"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_dest: "(t, as) \<in> ts_tuple_rel_f f ys \<Longrightarrow> \<exists>X. (t, X) \<in> ys \<and> as \<in> f X"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_Un: "ts_tuple_rel_f f (ys \<union> zs) = ts_tuple_rel_f f ys \<union> ts_tuple_rel_f f zs"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_ext: "tas \<in> ts_tuple_rel_f f {(nt, X)} \<Longrightarrow>
  \<forall> A B. f A \<union> f B = f (A \<union> B) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, Y \<union> X) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel_f f {(nt, X)}" "\<forall> A B. f A \<union> f B = f (A \<union> B)"
  then obtain as where tas_def: "tas = (nt, as)" "as \<in> f X"
    by (cases tas) (auto simp add: ts_tuple_rel_f_def)
  then have "as \<in> f (Y \<union> X)"
    using assm(2)
    by auto
  then show "tas \<in> ts_tuple_rel_f f (set ((nt, Y \<union> X) # tass))"
    unfolding tas_def(1)
    by (rule ts_tuple_rel_intro) auto
qed

lemma ts_tuple_rel_ext': "tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass)) \<Longrightarrow>
  \<forall> A B. f A \<union> f B = f (A \<union> B) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))" "\<forall> A B. f A \<union> f B = f (A \<union> B)"
  then have "tas \<in> ts_tuple_rel_f f {(nt, X)} \<union> ts_tuple_rel_f f (set tass)"
    using ts_tuple_rel_Un by force
  then show "tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
  proof
    assume "tas \<in> ts_tuple_rel_f f {(nt, X)}"
    then show ?thesis
      using assm(2)
      by (auto simp: Un_commute dest!: ts_tuple_rel_ext)
  next
    assume "tas \<in> ts_tuple_rel_f f (set tass)"
    then have "tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
      by (rule ts_tuple_rel_ext_Cons')
    then show ?thesis by simp
  qed
qed

lemma ts_tuple_rel_mono: "ys \<subseteq> zs \<Longrightarrow> ts_tuple_rel_f f ys \<subseteq> ts_tuple_rel_f f zs"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_filter: "ts_tuple_rel_f f (set (filter (\<lambda>(t, X). P t) xs)) =
  {(t, X) \<in> ts_tuple_rel_f f (set xs). P t}"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_set_filter: "x \<in> ts_tuple_rel_f f (set (filter P xs)) \<Longrightarrow>
  x \<in> ts_tuple_rel_f f (set xs)"
  by (auto simp add: ts_tuple_rel_f_def)

definition valid_tuple :: "(('a tuple, ts) mapping) \<Rightarrow> (ts \<times> 'a tuple) \<Rightarrow> bool" where
  "valid_tuple tuple_since = (\<lambda>(t, as). case Mapping.lookup tuple_since as of None \<Rightarrow> False
  | Some t' \<Rightarrow> t \<ge> t')"

definition safe_max :: "'a :: linorder set \<Rightarrow> 'a option" where
  "safe_max X = (if X = {} then None else Some (Max X))"

lemma safe_max_empty: "safe_max X = None \<longleftrightarrow> X = {}"
  by (simp add: safe_max_def)

lemma safe_max_empty_dest: "safe_max X = None \<Longrightarrow> X = {}"
  by (simp add: safe_max_def split: if_splits)

lemma safe_max_Some_intro: "x \<in> X \<Longrightarrow> \<exists>y. safe_max X = Some y"
  using safe_max_empty by auto

lemma safe_max_Some_dest_in: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> x \<in> X"
  using Max_in by (auto simp add: safe_max_def split: if_splits)

lemma safe_max_Some_dest_le: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> y \<in> X \<Longrightarrow> y \<le> x"
  using Max_ge by (auto simp add: safe_max_def split: if_splits)

definition newest_tuple_in_mapping :: "
  ('b \<Rightarrow> 'a table) \<Rightarrow>
  (ts \<times> 'b) queue \<Rightarrow>
  (('a tuple, ts) mapping) \<Rightarrow>
  ((ts \<times> 'a tuple) \<Rightarrow> bool) \<Rightarrow>
  bool"
  where
  "newest_tuple_in_mapping entry_to_db data_in tuple_in P = (\<forall>tuple.
    \<comment> \<open>iff something is present in the mapping then the value corresponds
       to the maximum timestamp of a db containing the tuple\<close>
    Mapping.lookup tuple_in tuple =
    safe_max (
      fst ` {
       tas \<in> ts_tuple_rel_f entry_to_db (set (linearize data_in)).
       P tas \<and> tuple = snd tas
      }
    )
  )"

lemma "newest_tuple_in_mapping entry_to_db data_in tuple_in (\<lambda>x. valid_tuple tuple_since x) =
  (\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel_f entry_to_db (set (linearize data_in)). valid_tuple tuple_since tas \<and> as = snd tas}))"
  by (auto simp add: newest_tuple_in_mapping_def)

fun valid_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a msaux \<Rightarrow> bool" where
  "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<longleftrightarrow>
    (args_L args) \<subseteq> (args_R args) \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    (\<forall>(t, X) \<in> set ys. table (args_n args) (args_R args) X) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_in) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_since) \<and>
    cur = nt \<and>
    (\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as) \<and>
    ts_tuple_rel (set ys) =
      {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
      valid_tuple tuple_since tas} \<and>
    sorted (map fst (linearize data_prev)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (args_ivl args) (nt - t)) \<and>
    sorted (map fst (linearize data_in)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> memL (args_ivl args) (nt - t)) \<and>
    newest_tuple_in_mapping id data_in tuple_in (\<lambda>x. valid_tuple tuple_since x)
  "

lemma Mapping_lookup_filter_keys: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  Mapping.lookup (Mapping.filter f m) k = Mapping.lookup m k"
  by (metis default_def insert_subset keys_default keys_filter lookup_default lookup_default_filter)

lemma Mapping_filter_keys: "(\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys (Mapping.filter f m). P (Mapping.lookup (Mapping.filter f m) k))"
  using Mapping_lookup_filter_keys Mapping.keys_filter by fastforce

lemma Mapping_filter_keys_le: "(\<And>x. P x \<Longrightarrow> P' x) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow> (\<forall>k \<in> Mapping.keys m. P' (Mapping.lookup m k))"
  by auto

lemma Mapping_keys_dest: "x \<in> Mapping.keys f \<Longrightarrow> \<exists>y. Mapping.lookup f x = Some y"
  by (simp add: domD keys_dom_lookup)

lemma Mapping_keys_intro: "Mapping.lookup f x \<noteq> None \<Longrightarrow> x \<in> Mapping.keys f"
  by (simp add: domIff keys_dom_lookup)

lemma valid_mmsaux_tuple_in_keys: "valid_mmsaux args cur
  (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<Longrightarrow>
  Mapping.keys tuple_in = snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
  valid_tuple tuple_since tas}"
  by (auto intro!: Mapping_keys_intro safe_max_Some_intro
      dest!: Mapping_keys_dest safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel]
      simp add: newest_tuple_in_mapping_def)+

fun init_mmsaux :: "args \<Rightarrow> 'a mmsaux" where
  "init_mmsaux args = (0, 0, join_mask (args_n args) (args_L args),
  join_mask (args_n args) (args_R args), empty_queue, empty_queue, Mapping.empty, Mapping.empty)"

lemma valid_init_mmsaux: "L \<subseteq> R \<Longrightarrow> valid_mmsaux (init_args I n L R b) 0
  (init_mmsaux (init_args I n L R b)) []"
  by (auto simp add: init_args_def empty_queue_rep ts_tuple_rel_f_def join_mask_def
      Mapping.lookup_empty safe_max_def table_def newest_tuple_in_mapping_def)

abbreviation "filter_cond X' ts t' \<equiv> (\<lambda>as _. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"
abbreviation "filter_cond' X' ts t' \<equiv> (\<lambda>as. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

lemma dropWhile_filter:
  "sorted (map fst xs) \<Longrightarrow>
  dropWhile (\<lambda>(t, X). \<not> memR I (nt - t)) xs = filter (\<lambda>(t, X). memR I (nt - t)) xs"
  by (induction xs) (auto 0 3 intro!: filter_id_conv[THEN iffD2, symmetric])

lemma dropWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow>
  dropWhile (\<lambda>(t, X). memL I (nt - t)) xs = filter (\<lambda>(t, X). \<not> memL I (nt - t)) xs"
  by (induction xs) (auto 0 3 simp: memL_mono diff_le_mono intro!: filter_id_conv[THEN iffD2, symmetric])

lemma takeWhile_filter:
  "sorted (map fst xs) \<Longrightarrow>
  takeWhile (\<lambda>(t, X). \<not> memR I (nt - t)) xs = filter (\<lambda>(t, X). \<not> memR I (nt - t)) xs"
  by (induction xs) (auto 0 3 simp: memR_antimono intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma takeWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow>
  takeWhile (\<lambda>(t, X). memL I (nt - t)) xs = filter (\<lambda>(t, X). memL I (nt - t)) xs"
  by (induction xs) (auto 0 3 simp: memL_mono intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma fold_Mapping_filter_None: "Mapping.lookup ts as = None \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter
  (filter_cond (f X) ts t) ts) ds ts) as = None"
  by (induction ds arbitrary: ts) (auto simp add: Mapping.lookup_filter)

lemma Mapping_lookup_filter_Some_P: "Mapping.lookup (Mapping.filter P m) k = Some v \<Longrightarrow> P k v"
  by (auto simp add: Mapping.lookup_filter split: option.splits if_splits)

lemma Mapping_lookup_filter_None: "(\<And>v. \<not>P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = None"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_Some: "(\<And>v. P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_not_None: "Mapping.lookup (Mapping.filter P m) k \<noteq> None \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma fold_Mapping_filter_Some_None: "Mapping.lookup ts as = Some t \<Longrightarrow>
  as \<in> (f X) \<Longrightarrow> (t, X) \<in> set ds \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond (f X) ts t) ts) ds ts) as = None"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using
        fold_Mapping_filter_None[of "Mapping.filter (filter_cond (f X') ts t') ts" as f ds]
        Mapping_lookup_filter_not_None[of "filter_cond (f X') ts t'" ts as]
        fold_Mapping_filter_None[OF Mapping_lookup_filter_None, of _ as f ds ts]
      by (cases "Mapping.lookup (Mapping.filter (filter_cond (f X') ts t') ts) as = None") auto
  qed
qed simp

lemma fold_Mapping_filter_Some_Some: "Mapping.lookup ts as = Some t \<Longrightarrow>
  (\<And>X. (t, X) \<in> set ds \<Longrightarrow> as \<notin> f X) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond (f X) ts t) ts) ds ts) as = Some t"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  then show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using Mapping_lookup_filter_Some[of "filter_cond (f X') ts t'" as ts] by auto
  qed
qed simp

(*
  1. drops from data_prev and data_in the entries that are no longer inside the interval
  2. for the dropped dbs from data_in we filter a mapping and remove all entries where the entry
     stored points to a dropped db (via the timestamp stored)
*)
fun shift_end :: "\<I> \<Rightarrow> ts \<Rightarrow> ('a \<Rightarrow> 'b table)  \<Rightarrow> ((ts \<times> 'c) queue \<times> (ts \<times> 'a) queue \<times> (('b tuple, ts) mapping) \<times> 'b table) \<Rightarrow> ((ts \<times> 'c) queue \<times> (ts \<times> 'a) queue \<times> (ts \<times> 'a) list \<times> (('b tuple, ts) mapping) \<times> 'b table)" where
  "shift_end I nt to_table (data_prev, data_in, tuple_in, tuple_in_keys) =
    (let
      data_prev = dropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_prev;
      (data_in, in_discard) = takedropWhile_queue (\<lambda>(t, _). \<not> memR I (nt - t)) data_in;
      (tuple_in, tuple_in_keys') = fold (\<lambda>(t, X) (tuple_in, tuple_in_keys). (
        (
          Mapping.filter (filter_cond (to_table X) tuple_in t) tuple_in,
          {as \<in> tuple_in_keys. (filter_cond' (to_table X) tuple_in t) as}
        )
      )) in_discard (tuple_in, tuple_in_keys) in
      (data_prev, data_in, in_discard, tuple_in, tuple_in_keys')
    )"

fun shift_end_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "shift_end_mmsaux args nt (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let (data_prev', data_in', _, tuple_in', _) =
      shift_end
      (args_ivl args)
      nt
      id
      (data_prev, data_in, tuple_in, {})
    in
    (t, gc, maskL, maskR, data_prev', data_in', tuple_in', tuple_since))"

lemma fold_pair_fst: "fst (fold (\<lambda> a (x, y). (f1 a x, f2 a x y)) as (x, y)) = fold (\<lambda> a (x). (f1 a x)) as (x)"
proof (induction as arbitrary: rule: rev_induct)
  case (snoc a as)
  then show ?case
    by (smt (z3) fold.simps(1) fold.simps(2) fold_append fst_conv id_o o_apply split_beta)
qed (auto)

(* since shift_end only affects data_prev, data_in & tuple_in, explicitly write the conditions out *)
lemma valid_shift_end_unfolded:
  assumes table_tuple_in: "table n V1 (Mapping.keys tuple_in)"
  assumes auxlist_tuples: "ts_tuple_rel_f f1_auxlist (set (filter_auxlist auxlist)) =
    {tas \<in> (ts_tuple_rel_f f1_prev (set (linearize data_prev))) \<union> (ts_tuple_rel_f f1_in (set (linearize data_in))).
    P1 tas}"
  assumes data_prev_props:
    "(\<forall>as \<in> \<Union>((f2 o snd) ` (set (linearize data_prev))). wf_tuple n V2 as)"
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> t' \<and> \<not> memL I (cur - t))"
  assumes data_in_props:
    "sorted (map fst (linearize data_in))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> t' \<and> memL I (cur - t))"
  assumes max_ts_tuple_in: "newest_tuple_in_mapping f3 data_in tuple_in P2"
  assumes nt_mono: "nt \<ge> cur" "t' \<le> nt"
  assumes shift_end_appl: "(data_prev', data_in', discard, tuple_in', tuple_in_keys') = shift_end I nt f3 (data_prev, data_in, tuple_in, tuple_in_keys)"
  shows
    "table n V1 (Mapping.keys tuple_in')"
    "ts_tuple_rel_f f1_auxlist (set (filter (\<lambda>(t, rel). memR I (nt - t)) (filter_auxlist auxlist))) =
    {tas \<in> (ts_tuple_rel_f f1_prev (set (linearize data_prev'))) \<union> (ts_tuple_rel_f f1_in (set (linearize data_in'))).
    P1 tas}"
    "(\<forall>as \<in> \<Union>((f2 o snd) ` (set (linearize data_prev'))). wf_tuple n V2 as)"
    "sorted (map fst (linearize data_prev'))"
    "(\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> t' \<and> \<not> memL I (cur - t))"
    "sorted (map fst (linearize data_in'))"
    "(\<forall>t \<in> fst ` set (linearize data_in'). t \<le> t' \<and> mem I (cur - t))"
    "newest_tuple_in_mapping f3 data_in' tuple_in' P2"
    "discard = snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
    "linearize data_in' = filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_in)"
    "tuple_in_keys = Mapping.keys tuple_in \<Longrightarrow> tuple_in_keys' = Mapping.keys tuple_in'"
    "tuple_in' = fold (\<lambda>(t, X) tuple_in. Mapping.filter
    (filter_cond (f3 X) tuple_in t) tuple_in) discard tuple_in"
proof -

  show discard_def: "discard = snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
    using shift_end_appl
    by (auto simp only: shift_end.simps Let_def snd_def split: prod.splits)

  have data_in'_def: "data_in' = fst (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
    using shift_end_appl
    by (auto simp only: shift_end.simps Let_def fst_def split: prod.splits)
  have data_prev'_def: "data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev"
    using shift_end_appl takedropWhile_queue_fst[of "(\<lambda>(t, X). \<not> memR I (nt - t))" data_prev]
    by (auto simp only: shift_end.simps Let_def fst_def split: prod.splits)

  have f_simp: "(\<lambda>a (x, y).
              ((case a of (t, X) \<Rightarrow> \<lambda>tuple_in. Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in) x,
               (case a of (t, X) \<Rightarrow> \<lambda>tuple_in tuple_in_keys. {as \<in> tuple_in_keys. filter_cond' (f3 X) tuple_in t as}) x y)) = 
      (\<lambda>(t, X) (tuple_in, tuple_in_keys). (Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in, {as \<in> tuple_in_keys. filter_cond' (f3 X) tuple_in t as}))"
    by auto

  have in_fold: "(tuple_in', tuple_in_keys') = fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (
        Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
        {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
      )
    ) discard (tuple_in, tuple_in_keys)"
    using shift_end_appl
    by (auto simp only: shift_end.simps Let_def snd_def split: prod.splits)
  then have "tuple_in' = fst (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (
        Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
        {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
      )
    ) discard (tuple_in, tuple_in_keys))"
    by (metis fstI)
  then show tuple_in'_def: "tuple_in' = fold (\<lambda>(t, X) tuple_in. Mapping.filter
    (filter_cond (f3 X) tuple_in t) tuple_in) discard tuple_in"
    using fold_pair_fst[of "\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in" "\<lambda>(t, X) tuple_in tuple_in_keys. {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}" discard tuple_in tuple_in_keys]
    by (auto simp only: f_simp)
  
  have tuple_in_Some_None: "\<And>as t X. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    (as) \<in> (f3 X) \<Longrightarrow> (t, X) \<in> set discard \<Longrightarrow> Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_Some_None unfolding tuple_in'_def by fastforce
  have tuple_in_Some_Some: "\<And>as t. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    (\<And>X. (t, X) \<in> set discard \<Longrightarrow> (as) \<notin> f3 X) \<Longrightarrow> Mapping.lookup tuple_in' as = Some t"
    using fold_Mapping_filter_Some_Some unfolding tuple_in'_def by force
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_None unfolding tuple_in'_def by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_Some_None tuple_in_Some_Some tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    using data_in_props nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    using data_prev_props nt_mono by auto
  show lin_data_in': "linearize data_in' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_in)"
    unfolding data_in'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F1(1)] thm dropWhile_filter[OF F1(1)] ..
  then have set_lin_data_in': "set (linearize data_in') \<subseteq> set (linearize data_in)"
    by auto
  show sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using sorted_filter data_in_props(1) by auto


  have discard_alt: "discard = filter (\<lambda>(t, X). \<not> memR I (nt - t)) (linearize data_in)"
    unfolding discard_def[unfolded takedropWhile_queue_snd] takeWhile_filter[OF F1(1)] ..
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F2(1)] ..
  show sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter data_prev_props(2) by auto


  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')). P2 tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')). P2 tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel_f f3 (set (linearize data_in)).
        P2 tas \<and> as = snd tas} = {}"
        using max_ts_tuple_in
        by (auto simp add: newest_tuple_in_mapping_def dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')).
        P2 tas \<and> as = snd tas} = {}"
        using ts_tuple_rel_mono[OF set_lin_data_in'] by auto
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      
      case (Some t)
      show ?thesis
      proof (cases "\<exists>X. (t, X) \<in> set discard \<and> (as) \<in> f3 X")
        case True
        then obtain X where X_def: "(t, X) \<in> set discard" "(as) \<in> f3 X"
          by auto
        have "\<not> memR I (nt - t)"
          using X_def(1) unfolding discard_alt by simp
        moreover have "\<And>t'. (t', as) \<in> ts_tuple_rel_f f3 (set (linearize data_in)) \<Longrightarrow>
          P2 (t', as) \<Longrightarrow> t' \<le> t"
          using max_ts_tuple_in Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff newest_tuple_in_mapping_def)
        ultimately have "{tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')).
          P2 tas \<and> as = snd tas} = {}"
          unfolding lin_data_in' using ts_tuple_rel_set_filter
          by (fastforce simp add: ts_tuple_rel_f_def memR_antimono)
        then show ?thesis
          unfolding tuple_in_Some_None[OF Some X_def(2,1)]
          using iffD2[OF safe_max_empty, symmetric] by blast
      next
        case False
        then have lookup_Some: "Mapping.lookup tuple_in' as = Some t"
          using tuple_in_Some_Some[OF Some] by auto
        have t_as: "(t, as) \<in> ts_tuple_rel_f f3 (set (linearize data_in))"
          "P2 (t, as)"
          using max_ts_tuple_in Some
          by (auto simp add: newest_tuple_in_mapping_def dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then obtain X where X_def: "as \<in> f3 X" "(t, X) \<in> set (linearize data_in)"
          by (auto simp add: ts_tuple_rel_f_def)
        have "(t, X) \<in> set (linearize data_in')"
          using X_def False unfolding discard_alt lin_data_in' by auto
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')).
          P2 tas \<and> as = snd tas}"
          using t_as(2) X_def(1) by (auto simp add: ts_tuple_rel_f_def image_iff)
        have "\<And>t'. (t', as) \<in> ts_tuple_rel_f f3 (set (linearize data_in)) \<Longrightarrow>
          P2 (t', as) \<Longrightarrow> t' \<le> t"
          using max_ts_tuple_in Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff newest_tuple_in_mapping_def)
        then have "Max (fst ` {tas \<in> ts_tuple_rel_f f3 (set (linearize data_in')).
          P2 tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel, OF _ t_in_fst]
            ts_tuple_rel_mono[OF set_lin_data_in'] by fastforce
        then show ?thesis
          unfolding lookup_Some using t_in_fst by (auto simp add: safe_max_def)
      qed
    qed
  qed

  then show "newest_tuple_in_mapping f3 data_in' tuple_in' P2"
    by (auto simp only: newest_tuple_in_mapping_def id_def)
  show table_in: "table n V1 (Mapping.keys tuple_in')"
    using tuple_in'_keys table_tuple_in
    by (auto simp add: table_def)

  show "(\<forall>as \<in> \<Union>((f2 o snd) ` (set (linearize data_prev'))). wf_tuple n V2 as)"
    using data_prev_props(1) lin_data_prev'
    by auto

  show
    "(\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> t' \<and> \<not> memL I (cur - t))"
    using lin_data_prev' data_prev_props
    by auto

  show
    "\<forall>t\<in>fst ` set (linearize data_in'). t \<le> t' \<and> mem I (cur - t)"
    using lin_data_in' data_in_props nt_mono
    by auto

  show "ts_tuple_rel_f f1_auxlist (set (filter (\<lambda>(t, rel). memR I (nt - t)) (filter_auxlist auxlist))) =
    {tas \<in> (ts_tuple_rel_f f1_prev (set (linearize data_prev'))) \<union> (ts_tuple_rel_f f1_in (set (linearize data_in'))).
    P1 tas}"
    using auxlist_tuples
    unfolding lin_data_prev' lin_data_in' ts_tuple_rel_Un ts_tuple_rel_filter
    by auto

  {
    define P::"(('a option list, ts) mapping \<times> 'a option list set) \<Rightarrow> bool" where "P = (\<lambda>(mapping, mapping_keys). mapping_keys = Mapping.keys mapping)"
    assume assm: "tuple_in_keys = Mapping.keys tuple_in"

    have "P (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
      (
        Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
        {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
      )
    ) discard (tuple_in, tuple_in_keys))"
    proof (induction discard rule: rev_induct)
      case Nil
      then show ?case using assm unfolding P_def by auto
    next
      case (snoc x xs)
      define induct where "induct = (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
        (
          Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
          {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
        )
      ) xs (tuple_in, tuple_in_keys))"
      define mapping where "mapping = fst induct"
      define keys where "keys = snd induct"

      have induct_eq: "induct = (mapping, keys)"
        unfolding mapping_def keys_def
        by auto

      define t where "t = fst x"
      define X where "X = snd x"

      have x_eq: "x = (t, X)"
        unfolding t_def X_def
        by auto

      define goal where "goal = (fold (\<lambda>(t, X) (tuple_in, tuple_in_keys).
        (
          Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
          {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
        )
      ) (xs @ [x]) (tuple_in, tuple_in_keys))"

      have goal_eq: "goal = (\<lambda>(t, X) (tuple_in, tuple_in_keys).
        (
          Mapping.filter (filter_cond (f3 X) tuple_in t) tuple_in,
          {as \<in> tuple_in_keys. (filter_cond' (f3 X) tuple_in t) as}
        )
      ) x induct"
        unfolding goal_def induct_def
        by auto
      then have goal_eq: "goal = (
          Mapping.filter (filter_cond (f3 X) mapping t) mapping,
          {as \<in> keys. (filter_cond' (f3 X) mapping t) as}
        )"
        unfolding x_eq induct_eq
        by auto

      have "P induct"
        using snoc
        unfolding induct_def
        by auto
      then have IH: "keys = Mapping.keys mapping"
        unfolding induct_eq P_def
        by auto

      have "{as \<in> keys. (filter_cond' (f3 X) mapping t) as} = Mapping.keys (Mapping.filter (filter_cond (f3 X) mapping t) mapping)"
      proof -
        {
          fix as
          assume "as \<in> {as \<in> keys. (filter_cond' (f3 X) mapping t) as}"
          then have "as \<in> keys" "(filter_cond' (f3 X) mapping t) as"
            by auto
          then have "as \<in> Mapping.keys (Mapping.filter (filter_cond (f3 X) mapping t) mapping)"
            unfolding IH
            by (smt (z3) Mapping_keys_dest Mapping_keys_intro Mapping_lookup_filter_Some option.simps(3))
        }
        moreover {
          fix as
          assume assm: "as \<in> Mapping.keys (Mapping.filter (filter_cond (f3 X) mapping t) mapping)"
          then have "as \<in> Mapping.keys mapping"
            by (smt (z3) Mapping_lookup_filter_not_None domIff keys_dom_lookup)
          moreover have "(filter_cond' (f3 X) mapping t) as"
            using assm
            by (metis (mono_tags, lifting) Mapping_lookup_filter_None domIff keys_dom_lookup)
          ultimately have "as \<in> {as \<in> keys. (filter_cond' (f3 X) mapping t) as}"
            unfolding IH[symmetric]
            by auto
        }
        ultimately show ?thesis by blast
      qed
      then have "P goal"
        unfolding P_def goal_eq
        by auto
      then show ?case unfolding goal_def by auto
    qed
    then have "P (tuple_in', tuple_in_keys')"
      unfolding in_fold
      by auto
    then show "tuple_in_keys' = Mapping.keys tuple_in'"
      unfolding P_def
      by auto
  }
qed


lemma valid_shift_end_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args cur (shift_end_mmsaux args nt
    (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof - 
  define shift_res where "shift_res = shift_end (args_ivl args) nt id (data_prev, data_in, tuple_in, {})"
  define data_prev' where "data_prev' = fst shift_res"
  define data_in' where "data_in' = (fst o snd) shift_res"
  define in_discard where "in_discard = (fst o snd o snd) shift_res"
  define tuple_in' where "tuple_in' = (fst o snd o snd o snd) shift_res"
  define tuple_in_keys' where "tuple_in_keys' = (snd o snd o snd o snd) shift_res"
  have shift_end_res: "(data_prev', data_in', in_discard, tuple_in', tuple_in_keys') = shift_end (args_ivl args) nt id (data_prev, data_in, tuple_in, {})"
    using data_prev'_def data_in'_def in_discard_def tuple_in'_def tuple_in_keys'_def shift_res_def
    by auto

  from assms(1) have table_tuple_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
    by auto

  from assms(1) have "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas}"
    by auto
  then have auxlist_tuples: "ts_tuple_rel (set (id auxlist)) =
    {tas \<in> (ts_tuple_rel (set (linearize data_prev)) \<union> (ts_tuple_rel (set (linearize data_in)))).
    valid_tuple tuple_since tas}"
    by (simp only: ts_tuple_rel_Un id_def)

  from assms(1) have
    "(\<forall>as \<in> \<Union>(snd ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> \<not> memL (args_ivl args) (cur - t))"
    by (auto simp only: valid_mmsaux.simps)

  then have data_prev_props:
    "(\<forall>as \<in> \<Union>((id o snd) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> \<not> memL (args_ivl args) (cur - t))"
    by auto
  
  from assms(1) have data_in_props:
    "sorted (map fst (linearize data_in))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> cur \<and> memL (args_ivl args) (cur - t))"
    by auto

  from assms(1) have max_ts_tuple_in: "newest_tuple_in_mapping id data_in tuple_in (\<lambda>x. valid_tuple tuple_since x)"
    by auto

  from assms(1) have time: "cur = ot" by auto

  have nt_mono: "nt \<ge> cur" "cur \<le> nt"
    using nt_mono
    by auto

  then have "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev', data_in', tuple_in', tuple_since)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
    using valid_before nt_mono
      valid_shift_end_unfolded [of
        "(args_n args)" "(args_R args)" tuple_in id id auxlist id data_prev id data_in
        "valid_tuple tuple_since",
        OF table_tuple_in auxlist_tuples data_prev_props
        data_in_props max_ts_tuple_in nt_mono shift_end_res
      ]
    by (auto simp only: valid_mmsaux.simps time) (auto simp add: ts_tuple_rel_Un)
  (* is slow *)

  moreover have "(ot, gc, maskL, maskR, data_prev', data_in', tuple_in', tuple_since) =
    shift_end_mmsaux args nt (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
    using shift_res_def
    by (auto simp only:
        shift_end_mmsaux.simps Let_def data_prev'_def data_in'_def tuple_in'_def fst_def snd_def o_def
        split: prod.splits
    )

  ultimately show ?thesis by auto
qed

lemma valid_shift_end_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args cur (shift_end_mmsaux args nt aux)
  (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_shift_end_mmsaux_unfolded by (cases aux) fast

setup_lifting type_definition_mapping

lift_definition upd_set :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m f X a. if a \<in> X then Some (f a) else m a" .

lemma Mapping_lookup_upd_set: "Mapping.lookup (upd_set m f X) a =
  (if a \<in> X then Some (f a) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set.rep_eq)

lemma Mapping_upd_set_keys: "Mapping.keys (upd_set m f X) = Mapping.keys m \<union> X"
  by (auto simp add: Mapping_lookup_upd_set dest!: Mapping_keys_dest intro: Mapping_keys_intro)

lift_definition upd_keys_on :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow>
  ('a, 'b) mapping" is
  "\<lambda>m f X a. case Mapping.lookup m a of Some b \<Rightarrow> Some (if a \<in> X then f a b else b)
  | None \<Rightarrow> None" .

lemma Mapping_lookup_upd_keys_on: "Mapping.lookup (upd_keys_on m f X) a =
  (case Mapping.lookup m a of Some b \<Rightarrow> Some (if a \<in> X then f a b else b) | None \<Rightarrow> None)"
  by (simp add: Mapping.lookup.rep_eq upd_keys_on.rep_eq)

lemma Mapping_upd_keys_sub: "Mapping.keys (upd_keys_on m f X) = Mapping.keys m"
  by (auto simp add: Mapping_lookup_upd_keys_on dest!: Mapping_keys_dest intro: Mapping_keys_intro
      split: option.splits)

lemma fold_append_queue_rep: "linearize (fold (\<lambda>x q. append_queue x q) xs q) = linearize q @ xs"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

lemma Max_Un_absorb:
  assumes "finite X" "X \<noteq> {}" "finite Y" "(\<And>x y. y \<in> Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<le> x)"
  shows "Max (X \<union> Y) = Max X"
proof -
  have Max_X_in_X: "Max X \<in> X"
    using Max_in[OF assms(1,2)] .
  have Max_X_in_XY: "Max X \<in> X \<union> Y"
    using Max_in[OF assms(1,2)] by auto
  have fin: "finite (X \<union> Y)"
    using assms(1,3) by auto
  have Y_le_Max_X: "\<And>y. y \<in> Y \<Longrightarrow> y \<le> Max X"
    using assms(4)[OF _ Max_X_in_X] .
  have XY_le_Max_X: "\<And>y. y \<in> X \<union> Y \<Longrightarrow> y \<le> Max X"
    using Max_ge[OF assms(1)] Y_le_Max_X by auto
  show ?thesis
    using Max_eqI[OF fin XY_le_Max_X Max_X_in_XY] by auto
qed

lemma Mapping_lookup_fold_upd_set_idle: "{(t, X) \<in> set xs. as \<in> Z X t} = {} \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as = Mapping.lookup m as"
proof (induction xs arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain x1 x2 where "x = (x1, x2)" by (cases x)
  have "Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs (upd_set m (\<lambda>_. x1) (Z x2 x1))) as =
    Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as"
    using Cons by auto
  also have "Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as = Mapping.lookup m as"
    using Cons.prems by (auto simp: \<open>x = (x1, x2)\<close> Mapping_lookup_upd_set)
  finally show ?case by (simp add: \<open>x = (x1, x2)\<close>)
qed

lemma Mapping_lookup_fold_upd_set_max: "{(t, X) \<in> set xs. as \<in> Z X t} \<noteq> {} \<Longrightarrow>
  sorted (map fst xs) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as =
  Some (Max (fst ` {(t, X) \<in> set xs. as \<in> Z X t}))"
proof (induction xs arbitrary: m)
  case (Cons x xs)
  obtain t X where tX_def: "x = (t, X)"
    by (cases x) auto
  have set_fst_eq: "(fst ` {(t, X). (t, X) \<in> set (x # xs) \<and> as \<in> Z X t}) =
    ((fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t}) \<union>
    (if as \<in> Z X t then {t} else {}))"
    using image_iff by (fastforce simp add: tX_def split: if_splits)
  show ?case
  proof (cases "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<noteq> {}")
    case True
    have "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<subseteq> set xs"
      by auto
    then have fin: "finite (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      by (simp add: finite_subset)
    have "Max (insert t (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})) =
      Max (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      using Max_Un_absorb[OF fin, of "{t}"] True Cons(3) tX_def by auto
    then show ?thesis
      using Cons True unfolding set_fst_eq by auto
  next
    case False
    then have empty: "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} = {}"
      by auto
    then have "as \<in> Z X t"
      using Cons(2) set_fst_eq by fastforce
    then show ?thesis
      using Mapping_lookup_fold_upd_set_idle[OF empty] unfolding set_fst_eq empty
      by (auto simp add: Mapping_lookup_upd_set tX_def)
  qed
qed simp
                                            
fun add_new_ts_past :: "\<I> \<Rightarrow> ts \<Rightarrow>
  ('a \<Rightarrow> 'b table) \<Rightarrow>
  ((ts \<times> 'a) queue \<times> (ts \<times> 'a) queue \<times> (('b tuple, ts) mapping) \<times> (('b tuple, ts) mapping)) \<Rightarrow>
  ((ts \<times> 'a) queue \<times> (ts \<times> 'a) queue \<times> (('b tuple, ts) mapping))
" where
  "add_new_ts_past I nt f (data_prev, data_in, tuple_in, tuple_since) =
    (let (data_prev, move) = takedropWhile_queue (\<lambda>(t, _). memL I (nt - t)) data_prev;
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    tuple_in = fold (\<lambda>(t, X) tuple_in. upd_set tuple_in (\<lambda>_. t)
      {as \<in> f X. valid_tuple tuple_since (t, as)}) move tuple_in in
    (data_prev, data_in, tuple_in)
  )"

fun add_new_ts_mmsaux' :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux' args nt (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) = (
    let (data_prev, data_in, tuple_in) = add_new_ts_past (args_ivl args) nt id (data_prev, data_in, tuple_in, tuple_since)
    in
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)
)"

lemma Mapping_keys_fold_upd_set: "k \<in> Mapping.keys (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z t X))
  xs m) \<Longrightarrow> k \<in> Mapping.keys m \<or> (\<exists>(t, X) \<in> set xs. k \<in> Z t X)"
  by (induction xs arbitrary: m) (fastforce simp add: Mapping_upd_set_keys)+

(* add_new_ts_mmsaux' only changes data_prev, data_in & tuple_in. write conditions explicitly *)
lemma valid_add_new_ts_past_unfolded:
  assumes table_tuple_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
  assumes auxlist_tuples: "ts_tuple_rel_f f (set auxlist) =
    {tas \<in> ts_tuple_rel_f f (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas}"
  assumes data_prev_props:
    "(\<forall>as \<in> \<Union>((f o snd) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> \<not> memL (args_ivl args) (cur - t))"
  assumes data_in_props:
    "sorted (map fst (linearize data_in))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> cur \<and> memL (args_ivl args) (cur - t))"
  assumes max_ts_tuple_in: "newest_tuple_in_mapping f data_in tuple_in (\<lambda>x. valid_tuple tuple_since x)"
  assumes nt_mono: "nt \<ge> cur"
  assumes add_new_ts_appl: "(data_prev', data_in', tuple_in') = add_new_ts_past (args_ivl args) nt f (data_prev, data_in, tuple_in, tuple_since)"
  shows
    "table (args_n args) (args_R args) (Mapping.keys tuple_in')"
    "\<forall>as \<in> \<Union>((f o snd) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as"
    "ts_tuple_rel_f f (set auxlist) =
    {tas \<in> ts_tuple_rel_f f (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since tas}"
    "sorted (map fst (linearize data_prev'))"
    "(\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> \<not> memL (args_ivl args) (nt - t))"
    "sorted (map fst (linearize data_in'))"
    "(\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> memL (args_ivl args) (nt - t))"
    "newest_tuple_in_mapping f data_in' tuple_in' (\<lambda>x. valid_tuple tuple_since x)"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  have data_prev'_def: "data_prev' = fst (takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev)"
    using add_new_ts_appl
    by (auto simp only: add_new_ts_past.simps Let_def fst_def I_def split: prod.splits)

  define move where "move \<equiv> snd (takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev)"

  have data_in'_def: "data_in' = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in"
    using add_new_ts_appl move_def
    by (auto simp only: add_new_ts_past.simps Let_def snd_def I_def split: prod.splits)

  have tuple_in'_def:  "tuple_in' = fold (\<lambda>(t, X) tuple_in. upd_set tuple_in (\<lambda>_. t)
      {as \<in> f X. valid_tuple tuple_since (t, as)}) move tuple_in"
    using add_new_ts_appl move_def
    by (auto simp only: add_new_ts_past.simps Let_def snd_def I_def split: prod.splits)

  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in \<or>
    (\<exists>(t, X)\<in>set move. as \<in> {as \<in> f X. valid_tuple tuple_since (t, as)})"
    using Mapping_keys_fold_upd_set[of _ "\<lambda>t X. {as \<in> f X. valid_tuple tuple_since (t, as)}"]
    by (auto simp add: tuple_in'_def)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_in). t \<le> cur \<and> memL I (cur - t)"
    using data_in_props nt_mono unfolding I_def by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> \<not> memL I (cur - t)"
    using data_prev_props nt_mono unfolding I_def by auto
 
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). \<not> memL I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep dropWhile_filter'[OF F2(1)]
    ..
  have move_filter: "move = filter (\<lambda>(t, X). memL I (nt - t)) (linearize data_prev)"
    unfolding move_def[unfolded takedropWhile_queue_snd] takeWhile_filter'[OF F2(1)] ..
  then have sorted_move: "sorted (map fst move)"
    using sorted_filter F2 by auto
  have "\<forall>t\<in>fst ` set move. t \<le> cur \<and> \<not> memL I (cur - t)"
    using move_filter F2(3) set_filter by auto
  then have fst_set_before: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t \<le> t'"
    using F1(3) by (meson le_diff_iff' memL_mono nat_le_linear)
  then have fst_ts_tuple_rel_before: "\<forall>t\<in>fst ` ts_tuple_rel_f f (set (linearize data_in)).
    \<forall>t'\<in>fst ` ts_tuple_rel_f f (set move). t \<le> t'"
    by (fastforce simp add: ts_tuple_rel_f_def)
  show sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter F2 by auto
  have lin_data_in': "linearize data_in' = linearize data_in @ move"
    unfolding data_in'_def using fold_append_queue_rep by fastforce
  show sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using F1(1) sorted_move fst_set_before by (simp add: sorted_append)
  have set_lin_prev'_in': "set (linearize data_prev') \<union> set (linearize data_in') =
    set (linearize data_prev) \<union> set (linearize data_in)"
    using lin_data_prev' lin_data_in' move_filter by auto
  show ts_tuple_rel': "ts_tuple_rel_f f (set auxlist) =
    {tas \<in> ts_tuple_rel_f f (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since tas}"
    unfolding set_lin_prev'_in' using auxlist_tuples by auto
  have lookup': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel_f f (set (linearize data_in')).
    valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel_f f (set (linearize data_in')).
      valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "{(t, X) \<in> set move. as \<in> f X \<and> valid_tuple tuple_since (t, as)} = {}")
      case True
      have move_absorb: "{tas \<in> ts_tuple_rel_f f (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        {tas \<in> ts_tuple_rel_f f (set (linearize data_in @ move)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        using True by (auto simp add: ts_tuple_rel_f_def)
      have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel_f f (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        using max_ts_tuple_in by (auto simp add: newest_tuple_in_mapping_def)
      then have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel_f f (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding lin_data_in' move_absorb .
      then show ?thesis
        using Mapping_lookup_fold_upd_set_idle[of "move" as
          "\<lambda>X t. {as \<in> f X. valid_tuple tuple_since (t, as)}"] True
        unfolding tuple_in'_def by auto
    next
      case False
      have split: "fst ` {tas \<in> ts_tuple_rel_f f (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        fst ` {tas \<in> ts_tuple_rel_f f (set move). valid_tuple tuple_since tas \<and> as = snd tas} \<union>
        fst ` {tas \<in> ts_tuple_rel_f f (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        unfolding lin_data_in' set_append ts_tuple_rel_Un by auto
      have max_eq: "Max (fst ` {tas \<in> ts_tuple_rel_f f (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}) =
        Max (fst ` {tas \<in> ts_tuple_rel_f f (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding split using False fst_ts_tuple_rel_before
        by (fastforce simp add: ts_tuple_rel_f_def
            intro!: Max_Un_absorb[OF finite_fst_ts_tuple_rel _ finite_fst_ts_tuple_rel, symmetric])
      have "fst ` {(t, X). (t, X) \<in> set move \<and> as \<in> {as \<in> f X. valid_tuple tuple_since (t, as)}} =
        fst ` {tas \<in> ts_tuple_rel_f f (set move). valid_tuple tuple_since tas \<and> as = snd tas}"
        by (auto simp add: ts_tuple_rel_f_def image_iff)
      then have "Mapping.lookup tuple_in' as = Some (Max (fst ` {tas \<in> ts_tuple_rel_f f (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}))"
        using Mapping_lookup_fold_upd_set_max[of "move" as
          "\<lambda>X t. {as \<in> f X. valid_tuple tuple_since (t, as)}", OF _ sorted_move] False
        unfolding tuple_in'_def by (auto simp add: ts_tuple_rel_f_def)
      then show ?thesis
        unfolding max_eq using False
        by (auto simp add: safe_max_def lin_data_in' ts_tuple_rel_f_def)
    qed
  qed
  then show "newest_tuple_in_mapping f data_in' tuple_in' (\<lambda>x. valid_tuple tuple_since x)"
    by (auto simp only: newest_tuple_in_mapping_def id_def)

  have table_in': "table n R (Mapping.keys tuple_in')"
  proof -
    {
      fix as
      assume assm: "as \<in> Mapping.keys tuple_in'"
      have "wf_tuple n R as"
        using tuple_in'_keys[OF assm]
      proof (rule disjE)
        assume "as \<in> Mapping.keys tuple_in"
        then show "wf_tuple n R as"
          using table_tuple_in by (auto simp add: table_def n_def R_def)
      next
        assume "\<exists>(t, X)\<in>set move. as \<in> {as \<in> f X. valid_tuple tuple_since (t, as)}"
        then obtain t X where tX_def: "(t, X) \<in> set move" "as \<in> f X"
          by auto
        then have "(t, X) \<in> set (takeWhile (\<lambda>(t, X). memL I (nt - t)) (linearize data_prev))"
          unfolding move_def using takedropWhile_queue_snd[of "(\<lambda>(t, X). memL I (nt - t))" data_prev]
          by auto
        then have "as \<in> \<Union>((f o snd) ` set (linearize data_prev))"
          unfolding move_def using set_takeWhileD tX_def by force
        then show "wf_tuple n R as"
          using data_prev_props(1)
          by (auto simp add: n_def R_def)
      qed
    }
    then show ?thesis
      by (auto simp add: table_def)
  qed

  then show "table (args_n args) (args_R args) (Mapping.keys tuple_in')"
    using n_def R_def
    by auto

  have data_prev'_move: "(data_prev', move) =
    takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev"
    using takedropWhile_queue_fst takedropWhile_queue_snd data_prev'_def move_def
    by (metis surjective_pairing)

  have "(\<forall>as \<in> \<Union>((f o snd) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    using data_prev_props
    by auto

  show "\<forall>as \<in> \<Union>((f o snd) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as"
    using data_prev_props lin_data_prev'
    by auto

  show "(\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> \<not> memL (args_ivl args) (nt - t))"
    using data_prev_props lin_data_prev' nt_mono
    unfolding I_def
    by auto

  show "(\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> memL (args_ivl args) (nt - t))"
    using lin_data_in' move_filter nt_mono data_in_props data_prev_props unfolding I_def
    (* by (auto simp add: memL_mono) is slower *)
    by (smt I_def Un_iff case_prod_beta' diff_commute diff_diff_cancel diff_le_self imageE image_eqI le_trans memL_mono move_def set_append set_takeWhileD takedropWhile_queue_snd)
qed

lemma valid_add_new_ts_mmsaux'_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux' args nt
    (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)) auxlist"
proof -
  define res where "res = add_new_ts_past (args_ivl args) nt id (data_prev, data_in, tuple_in, tuple_since)"
  define data_prev' where "data_prev' = fst res"
  define data_in' where "data_in' = (fst o snd) res"
  define tuple_in' where "tuple_in' = (snd o snd) res"
  have t: "cur = ot" using assms(1) by auto

  have shift_end_res: "(data_prev', data_in', tuple_in') = add_new_ts_past (args_ivl args) nt id (data_prev, data_in, tuple_in, tuple_since)"
    using data_prev'_def data_in'_def tuple_in'_def res_def
    by auto

  have table_tuple_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
    using assms(1)
    by auto
  have auxlist_tuples: "ts_tuple_rel_f id (set auxlist) =
    {tas \<in> ts_tuple_rel_f id (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas}"
    using assms(1)
    by auto

  have data_prev_props:
    "(\<forall>as \<in> \<Union>((id o snd) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> \<not> memL (args_ivl args) (cur - t))"
    using assms(1)
    by auto

  have data_in_props:
    "sorted (map fst (linearize data_in))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> cur \<and> memL (args_ivl args) (cur - t))"
    using assms(1)
    by auto

  have max_ts_tuple_in: "newest_tuple_in_mapping id data_in tuple_in (\<lambda>x. valid_tuple tuple_since x)"
    using assms(1)
    by auto

  have since_map: "\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> ot"
    using assms(1)
    by auto
  {
    fix as
    assume assm: "as \<in> Mapping.keys tuple_since" "case Mapping.lookup tuple_since as of Some t \<Rightarrow> True"
    then have "case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt"
    proof (cases "Mapping.lookup tuple_since as")
      case None
      then show ?thesis using since_map assm by auto
    next
      case (Some t)
      then have "t \<le> ot" using since_map assm by auto
      then have "t \<le> nt" using nt_mono t by auto
      then show ?thesis using Some by auto
    qed
  }
  then have "\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt"
    using Mapping_keys_dest by fastforce


  then have "valid_mmsaux args nt (nt, gc, maskL, maskR, data_prev', data_in', tuple_in', tuple_since) auxlist"
    using valid_add_new_ts_past_unfolded[OF table_tuple_in auxlist_tuples data_prev_props
          data_in_props max_ts_tuple_in nt_mono shift_end_res] assms(1)
    by (auto simp only: valid_mmsaux.simps) (auto)
    (* is slow *)

  moreover have "(nt, gc, maskL, maskR, data_prev', data_in', tuple_in', tuple_since) =
    add_new_ts_mmsaux' args nt (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
    by (auto simp only:
        add_new_ts_mmsaux'.simps Let_def data_prev'_def data_in'_def tuple_in'_def res_def fst_def snd_def o_def
        split: prod.splits
    )

  ultimately show ?thesis by auto 
qed

lemma valid_add_new_ts_mmsaux': "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args nt (add_new_ts_mmsaux' args nt aux) auxlist"
  using valid_add_new_ts_mmsaux'_unfolded by (cases aux) fast

definition add_new_ts_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux args nt aux = add_new_ts_mmsaux' args nt (shift_end_mmsaux args nt aux)"

lemma valid_add_new_ts_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_add_new_ts_mmsaux'[OF valid_shift_end_mmsaux[OF assms] assms(2)]
  unfolding add_new_ts_mmsaux_def .

fun join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let pos = args_pos args in
    (if maskL = maskR then
      (let tuple_in = Mapping.filter (join_filter_cond pos X) tuple_in;
      tuple_since = Mapping.filter (join_filter_cond pos X) tuple_since in
      (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    else if (\<forall>i \<in> set maskL. \<not>i) then
      (let nones = replicate (length maskL) None;
      take_all = (pos \<longleftrightarrow> nones \<in> X);
      tuple_in = (if take_all then tuple_in else Mapping.empty);
      tuple_since = (if take_all then tuple_since else Mapping.empty) in
      (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    else
      (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
      tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
      (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))))"

fun join_mmsaux_abs :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux_abs args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let pos = args_pos args in
    (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
    tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
    (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)))"

lemma Mapping_filter_cong:
  assumes cong: "(\<And>k v. k \<in> Mapping.keys m \<Longrightarrow> f k v = f' k v)"
  shows "Mapping.filter f m = Mapping.filter f' m"
proof -
  have "\<And>k. Mapping.lookup (Mapping.filter f m) k = Mapping.lookup (Mapping.filter f' m) k"
    using cong
    by (fastforce simp add: Mapping.lookup_filter intro: Mapping_keys_intro split: option.splits)
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma join_mmsaux_abs_eq:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_left: "table (args_n args) (args_L args) X"
  shows "join_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    join_mmsaux_abs args X (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
proof (cases "maskL = maskR")
  case True
  define n where "n = args_n args"
  define L where "L = args_L args"
  define pos where "pos = args_pos args"
  have keys_wf_in: "\<And>as. as \<in> Mapping.keys tuple_in \<Longrightarrow> wf_tuple n L as"
    using wf_tuple_change_base valid_before True by (fastforce simp add: table_def n_def L_def)
  have cong_in: "\<And>as n. as \<in> Mapping.keys tuple_in \<Longrightarrow>
    proj_tuple_in_join pos maskL as X \<longleftrightarrow> join_cond pos X as"
    using proj_tuple_in_join_mask_idle[OF keys_wf_in] valid_before
    by (auto simp only: valid_mmsaux.simps n_def L_def pos_def)
  have keys_wf_since: "\<And>as. as \<in> Mapping.keys tuple_since \<Longrightarrow> wf_tuple n L as"
    using wf_tuple_change_base valid_before True by (fastforce simp add: table_def n_def L_def)
  have cong_since: "\<And>as n. as \<in> Mapping.keys tuple_since \<Longrightarrow>
    proj_tuple_in_join pos maskL as X \<longleftrightarrow> join_cond pos X as"
    using proj_tuple_in_join_mask_idle[OF keys_wf_since] valid_before
    by (auto simp only: valid_mmsaux.simps n_def L_def pos_def)
  show ?thesis
    using True Mapping_filter_cong[OF cong_in, of tuple_in "\<lambda>k _. k"]
      Mapping_filter_cong[OF cong_since, of tuple_since "\<lambda>k _. k"]
    by (auto simp add: pos_def)
next
  case False
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  from False show ?thesis
  proof (cases "\<forall>i \<in> set maskL. \<not>i")
    case True
    have length_maskL: "length maskL = n"
      using valid_before by (auto simp add: join_mask_def n_def)
    have proj_rep: "\<And>as. wf_tuple n R as \<Longrightarrow> proj_tuple maskL as = replicate (length maskL) None"
      using True proj_tuple_replicate by (force simp add: length_maskL wf_tuple_def)
    have keys_wf_in: "\<And>as. as \<in> Mapping.keys tuple_in \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def n_def R_def)
    have keys_wf_since: "\<And>as. as \<in> Mapping.keys tuple_since \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def n_def R_def)
    have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_in) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_in else Mapping.empty) as"
      using proj_rep[OF keys_wf_in]
      by (auto simp add: Mapping.lookup_filter Mapping.lookup_empty proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    moreover have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_since) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_since else Mapping.empty) as"
      using proj_rep[OF keys_wf_since]
      by (auto simp add: Mapping.lookup_filter Mapping.lookup_empty proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using False True by (auto simp add: mapping_eqI Let_def pos_def)
  qed (auto simp add: Let_def)
qed

lemma valid_join_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_left': "table (args_n args) (args_L args) X"
  shows "valid_mmsaux args cur
    (join_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  note table_left = table_left'[unfolded n_def[symmetric] L_def[symmetric]]
  define tuple_in' where "tuple_in' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in"
  define tuple_since' where "tuple_since' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since"
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    unfolding tuple_in'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have ts_tuple_rel': "ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
    then obtain t as Z where tas_def: "tas = (t, as)" "as \<in> join Z pos X" "(t, Z) \<in> set auxlist"
      "(t, join Z pos X) \<in> set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
      by (fastforce simp add: ts_tuple_rel_f_def)
    from tas_def(3) have table_Z: "table n R Z"
      using valid_before by (auto simp add: n_def R_def)
    have proj: "as \<in> Z" "proj_tuple_in_join pos maskL as X"
      using tas_def(2) join_sub[OF _ table_left table_Z] valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    then have "(t, as) \<in> ts_tuple_rel (set (auxlist))"
      using tas_def(3) by (auto simp add: ts_tuple_rel_f_def)
    then have tas_in: "(t, as) \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in))" "valid_tuple tuple_since (t, as)"
      using valid_before by auto
    then obtain t' where t'_def: "Mapping.lookup tuple_since as = Some t'" "t \<ge> t'"
      by (auto simp add: valid_tuple_def split: option.splits)
    then have valid_tuple_since': "valid_tuple tuple_since' (t, as)"
      using proj(2)
      by (auto simp add: tuple_since'_def Mapping_lookup_filter_Some valid_tuple_def)
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
      valid_tuple tuple_since' tas}"
      using tas_in valid_tuple_since' unfolding tas_def(1)[symmetric] by auto
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in)). valid_tuple tuple_since' tas}"
    then obtain t as where tas_def: "tas = (t, as)" "valid_tuple tuple_since' (t, as)"
      by (auto simp add: ts_tuple_rel_f_def)
    from tas_def(2) have "valid_tuple tuple_since (t, as)"
      unfolding tuple_since'_def using Mapping_lookup_filter_not_None
      by (force simp add: valid_tuple_def split: option.splits)
    then have "(t, as) \<in> ts_tuple_rel (set auxlist)"
      using valid_before assm tas_def(1) by auto
    then obtain Z where Z_def: "as \<in> Z" "(t, Z) \<in> set auxlist"
      by (auto simp add: ts_tuple_rel_f_def)
    then have table_Z: "table n R Z"
      using valid_before by (auto simp add: n_def R_def)
    from tas_def(2) have "proj_tuple_in_join pos maskL as X"
      unfolding tuple_since'_def using Mapping_lookup_filter_Some_P
      by (fastforce simp add: valid_tuple_def split: option.splits)
    then have as_in_join: "as \<in> join Z pos X"
      using join_sub[OF _ table_left table_Z] Z_def(1) valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    then show "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
      using Z_def unfolding tas_def(1) by (auto simp add: ts_tuple_rel_f_def)
  qed
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before
        by (auto simp add: newest_tuple_in_mapping_def dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas} = {}"
        using Mapping_lookup_filter_not_None
        by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric]
        by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "proj_tuple_in_join pos maskL as X")
        case True
        then have lookup_tuple_in': "Mapping.lookup tuple_in' as = Some t"
          using Some unfolding tuple_in'_def by (simp add: Mapping_lookup_filter_Some)
        have "(t, as) \<in> ts_tuple_rel (set (linearize data_in))" "valid_tuple tuple_since (t, as)"
          using valid_before Some
          by (auto simp add: newest_tuple_in_mapping_def dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using True by (auto simp add: image_iff valid_tuple_def tuple_since'_def
            Mapping_lookup_filter_Some split: option.splits)
        have "\<And>t'. valid_tuple tuple_since' (t', as) \<Longrightarrow> valid_tuple tuple_since (t', as)"
          using Mapping_lookup_filter_not_None
          by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
        then have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since' (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff newest_tuple_in_mapping_def)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of _ "linearize data_in"],
            OF _ t_in_fst] by fastforce
        then show ?thesis
          unfolding lookup_tuple_in' using t_in_fst by (auto simp add: safe_max_def)
      next
        case False
        then have lookup_tuple': "Mapping.lookup tuple_in' as = None"
          "Mapping.lookup tuple_since' as = None"
          unfolding tuple_in'_def tuple_since'_def
          by (auto simp add: Mapping_lookup_filter_None)
        then have "\<And>tas. \<not>(valid_tuple tuple_since' tas \<and> as = snd tas)"
          by (auto simp add: valid_tuple_def split: option.splits)
        then show ?thesis
          unfolding lookup_tuple' by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_join': "\<And>t ys. (t, ys) \<in> set auxlist \<Longrightarrow> table n R (join ys pos X)"
  proof -
    fix t ys
    assume "(t, ys) \<in> set auxlist"
    then have table_ys: "table n R ys"
      using valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    show "table n R (join ys pos X)"
      using join_table[OF table_ys table_left, of pos R] valid_before
      by (auto simp add: n_def L_def R_def pos_def)
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using tuple_since'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  show ?thesis
    unfolding join_mmsaux_abs_eq[OF valid_before table_left']
    using valid_before ts_tuple_rel' lookup_tuple_in' tuple_in'_def tuple_since'_def table_join'
      Mapping_filter_keys[of tuple_since "\<lambda>as. case as of Some t \<Rightarrow> t \<le> nt"]
      table_in' table_since'
    by (auto simp add: n_def L_def R_def pos_def table_def Let_def newest_tuple_in_mapping_def)
qed

lemma valid_join_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  table (args_n args) (args_L args) X \<Longrightarrow> valid_mmsaux args cur
  (join_mmsaux args X aux) (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
  using valid_join_mmsaux_unfolded by (cases aux) fast

fun gc_mmsaux :: "'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_mmsaux (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
    tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
    (nt, nt, maskL, maskR, data_prev, data_in, tuple_in, tuple_since'))"

lemma valid_gc_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since) ys"
  shows "valid_mmsaux args cur (gc_mmsaux (nt, gc, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since)) ys"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define all_tuples where "all_tuples \<equiv> \<Union>(snd ` (set (linearize data_prev) \<union>
    set (linearize data_in)))"
  define tuple_since' where "tuple_since' \<equiv> Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since"
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  then have table_since': "table n R (Mapping.keys tuple_since')"
    using valid_before by (auto simp add: table_def n_def R_def)
  have data_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in)) \<Longrightarrow> valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
  proof -
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in))"
    define t where "t \<equiv> fst tas"
    define as where "as \<equiv> snd tas"
    have "as \<in> all_tuples"
      using assm by (force simp add: as_def all_tuples_def ts_tuple_rel_f_def)
    then have "Mapping.lookup tuple_since' as = Mapping.lookup tuple_since as"
      by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits)
    then show "valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
      by (auto simp add: valid_tuple_def as_def split: option.splits) metis
  qed
  then have data_in_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
    valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
    by (auto simp add: ts_tuple_rel_Un)
  have "ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
    using data_cong valid_before by auto
  moreover have "(\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas}))"
    using valid_before by (auto simp add: newest_tuple_in_mapping_def) (meson data_in_cong)
  moreover have "(\<forall>as \<in> Mapping.keys tuple_since'. case Mapping.lookup tuple_since' as of
    Some t \<Rightarrow> t \<le> nt)"
    using Mapping.keys_filter valid_before
    by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits
        intro!: Mapping_keys_intro dest: Mapping_keys_dest)
  ultimately show ?thesis
    using all_tuples_def tuple_since'_def valid_before table_since'
    by (auto simp add: n_def R_def newest_tuple_in_mapping_def)
qed

lemma valid_gc_mmsaux: "valid_mmsaux args cur aux ys \<Longrightarrow> valid_mmsaux args cur (gc_mmsaux aux) ys"
  using valid_gc_mmsaux_unfolded by (cases aux) fast

fun gc_join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (if \<not> memR (args_ivl args) (t - gc) then join_mmsaux args X (gc_mmsaux (t, gc, maskL, maskR,
      data_prev, data_in, tuple_in, tuple_since))
    else join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))"

lemma gc_join_mmsaux_alt: "gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 (gc_mmsaux aux) \<or>
  gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 aux"
  by (cases aux) (auto simp only: gc_join_mmsaux.simps split: if_splits)

lemma valid_gc_join_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "table (args_n args) (args_L args) rel1"
  shows "valid_mmsaux args cur (gc_join_mmsaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
  using gc_join_mmsaux_alt[of args rel1 aux]
  using valid_join_mmsaux[OF valid_gc_mmsaux[OF assms(1)] assms(2)]
    valid_join_mmsaux[OF assms]
  by auto

fun add_new_table_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_table_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let tuple_since = upd_set tuple_since (\<lambda>_. t) (X - Mapping.keys tuple_since) in
    (if memL (args_ivl args) 0 then (t, gc, maskL, maskR, data_prev, append_queue (t, X) data_in,
      upd_set tuple_in (\<lambda>_. t) X, tuple_since)
    else (t, gc, maskL, maskR, append_queue (t, X) data_prev, data_in, tuple_in, tuple_since)))"

lemma valid_add_new_table_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
proof -
  have cur_nt: "cur = nt"
    using valid_before by auto
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define tuple_in' where "tuple_in' \<equiv> upd_set tuple_in (\<lambda>_. nt) X"
  define tuple_since' where "tuple_since' \<equiv> upd_set tuple_since (\<lambda>_. nt)
    (X - Mapping.keys tuple_since)"
  define data_prev' where "data_prev' \<equiv> append_queue (nt, X) data_prev"
  define data_in' where "data_in' \<equiv> append_queue (nt, X) data_in"
  define auxlist' where "auxlist' \<equiv> (case auxlist of
    [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  have table_in': "table n R (Mapping.keys tuple_in')"
    using table_X valid_before
    by (auto simp add: table_def tuple_in'_def Mapping_upd_set_keys n_def R_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using table_X valid_before
    by (auto simp add: table_def tuple_since'_def Mapping_upd_set_keys n_def R_def)
  have tuple_since'_keys: "Mapping.keys tuple_since \<subseteq> Mapping.keys tuple_since'"
    using Mapping_upd_set_keys by (fastforce simp add: tuple_since'_def)
  have lin_data_prev': "linearize data_prev' = linearize data_prev @ [(nt, X)]"
    unfolding data_prev'_def append_queue_rep ..
  have wf_data_prev': "\<And>as. as \<in> \<Union>(snd ` (set (linearize data_prev'))) \<Longrightarrow> wf_tuple n R as"
    unfolding lin_data_prev' using table_X valid_before
    by (auto simp add: table_def n_def R_def)
  have lin_data_in': "linearize data_in' = linearize data_in @ [(nt, X)]"
    unfolding data_in'_def append_queue_rep ..
  have table_auxlist': "\<forall>(t, X) \<in> set auxlist'. table n R X"
    using table_X table_Un valid_before
    by (auto simp add: auxlist'_def n_def R_def split: list.splits if_splits)
  have lookup_tuple_since': "\<forall>as \<in> Mapping.keys tuple_since'.
    case Mapping.lookup tuple_since' as of Some t \<Rightarrow> t \<le> nt"
    unfolding tuple_since'_def using valid_before Mapping_lookup_upd_set[of tuple_since]
    by (auto dest: Mapping_keys_dest intro!: Mapping_keys_intro split: if_splits option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    ts_tuple_rel (set auxlist) \<union> ts_tuple_rel {(nt, X)}"
    unfolding auxlist'_def
    using ts_tuple_rel_ext[of _ id] ts_tuple_rel_ext'[of _ id]
      ts_tuple_rel_ext_Cons ts_tuple_rel_ext_Cons'
    by (fastforce simp: ts_tuple_rel_f_def split: list.splits if_splits)
  have valid_tuple_nt_X: "\<And>tas. tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow> valid_tuple tuple_since' tas"
    using valid_before by (auto simp add: ts_tuple_rel_f_def valid_tuple_def tuple_since'_def
        Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
  have valid_tuple_mono: "\<And>tas. valid_tuple tuple_since tas \<Longrightarrow> valid_tuple tuple_since' tas"
    by (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
        intro: Mapping_keys_intro split: option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in) \<union> {(nt, X)}).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set auxlist')"
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
      using assm[unfolded ts_tuple_rel_auxlist' ts_tuple_rel_Un]
    proof (rule UnE)
      assume assm: "tas \<in> ts_tuple_rel (set auxlist)"
      then have "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)). valid_tuple tuple_since tas}"
        using valid_before by auto
      then show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm by (auto simp only: ts_tuple_rel_Un intro: valid_tuple_mono)
    next
      assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm valid_before by (auto simp add: ts_tuple_rel_Un tuple_since'_def
            valid_tuple_def Mapping_lookup_upd_set ts_tuple_rel_f_def dest: Mapping_keys_dest
            split: option.splits if_splits)
    qed
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
    then have "tas \<in> (ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in)) - ts_tuple_rel {(nt, X)}) \<union> ts_tuple_rel {(nt, X)}"
      by (auto simp only: ts_tuple_rel_Un)
    then show "tas \<in> ts_tuple_rel (set auxlist')"
    proof (rule UnE)
      assume assm': "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)) - ts_tuple_rel {(nt, X)}"
      then have tas_in: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in))"
        by (auto simp only: ts_tuple_rel_f_def)
      obtain t as where tas_def: "tas = (t, as)"
        by (cases tas) auto
      have "t \<in> fst ` (set (linearize data_prev) \<union> set (linearize data_in))"
        using assm' unfolding tas_def by (force simp add: ts_tuple_rel_f_def)
      then have t_le_nt: "t \<le> nt"
        using valid_before by auto
      have valid_tas: "valid_tuple tuple_since' tas"
        using assm by auto
      have "valid_tuple tuple_since tas"
      proof (cases "as \<in> Mapping.keys tuple_since")
        case True
        then show ?thesis
          using valid_tas tas_def by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set split: option.splits if_splits)
      next
        case False
        then have "t = nt" "as \<in> X"
          using valid_tas t_le_nt unfolding tas_def
          by (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
              intro: Mapping_keys_intro split: option.splits if_splits)
        then have "False"
          using assm' unfolding tas_def ts_tuple_rel_f_def by (auto simp only: ts_tuple_rel_f_def id_def)
        then show ?thesis
          by simp
      qed
      then show "tas \<in> ts_tuple_rel (set auxlist')"
        using tas_in valid_before by (auto simp add: ts_tuple_rel_auxlist')
    qed (auto simp only: ts_tuple_rel_auxlist')
  qed
  show ?thesis
  proof (cases "memL I 0")
    case True
    then have add_def: "add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since) = (nt, gc, maskL, maskR, data_prev, data_in',
      tuple_in', tuple_since')"
      using data_in'_def tuple_in'_def tuple_since'_def unfolding I_def by auto
    have "\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> memL I (nt - t)"
      using valid_before True by (auto simp add: lin_data_in')
    moreover have "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof -
      fix as
      show "Mapping.lookup tuple_in' as = safe_max (fst `
        {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since' tas \<and> as = snd tas})"
      proof (cases "as \<in> X")
        case True
        have "valid_tuple tuple_since' (nt, as)"
          using True valid_before by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
        moreover have "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          using True by (auto simp add: ts_tuple_rel_f_def)
        ultimately have nt_in: "nt \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas}"
        proof -
          assume a1: "valid_tuple tuple_since' (nt, as)"
          assume "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          then have "\<exists>p. nt = fst p \<and> p \<in> ts_tuple_rel (insert (nt, X)
            (set (linearize data_in))) \<and> valid_tuple tuple_since' p \<and> as = snd p"
            using a1 by simp
          then show "nt \<in> fst ` {p \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in))).
            valid_tuple tuple_since' p \<and> as = snd p}"
            by blast
        qed
        moreover have "\<And>t. t \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas} \<Longrightarrow> t \<le> nt"
          using valid_before by (auto split: option.splits)
            (metis (no_types, lifting) eq_imp_le fst_conv insertE ts_tuple_rel_dest)
        ultimately have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)
          \<union> set [(nt, X)]). valid_tuple tuple_since' tas \<and> as = snd tas}) = nt"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of _ "linearize data_in'"],
              unfolded lin_data_in' set_append]
          by (metis (mono_tags) Un_empty_right Un_insert_right empty_set list.simps(15))
        then show ?thesis
          using nt_in True
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set safe_max_def lin_data_in')
      next
        case False
        have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since tas \<and> as = snd tas} =
          {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using False by (fastforce simp add: lin_data_in' ts_tuple_rel_f_def valid_tuple_def
              tuple_since'_def Mapping_lookup_upd_set intro: Mapping_keys_intro
              split: option.splits if_splits)
        then show ?thesis
          using valid_before False
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set newest_tuple_in_mapping_def)
      qed
    qed
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_in)"]
        lookup_tuple_since' ts_tuple_rel_auxlist' table_in' table_since'
      unfolding add_def auxlist'_def[symmetric] cur_nt I_def
      by (auto simp only: valid_mmsaux.simps lin_data_in' n_def R_def newest_tuple_in_mapping_def)
          auto
  next
    case False
    then have add_def: "add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since) = (nt, gc, maskL, maskR, data_prev', data_in,
      tuple_in, tuple_since')"
      using data_prev'_def tuple_since'_def unfolding I_def by auto
    have "\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> \<not> memL I (nt - t)"
      using valid_before False by (auto simp add: lin_data_prev' I_def)
    moreover have "\<And>as. {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since tas \<and> as = snd tas} =
      {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since' tas \<and> as = snd tas}"
    proof (rule set_eqI, rule iffI)
      fix as tas
      assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas}"
      then obtain t Z where Z_def: "tas = (t, as)" "as \<in> Z" "(t, Z) \<in> set (linearize data_in)"
        "valid_tuple tuple_since' (t, as)"
        by (auto simp add: ts_tuple_rel_f_def)
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
      using assm
      proof (cases "as \<in> Mapping.keys tuple_since")
        case False
        then have "t \<ge> nt"
          using Z_def(4) by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set intro: Mapping_keys_intro split: option.splits if_splits)
        then show ?thesis
          using Z_def(3) valid_before \<open>\<not> memL I 0\<close> unfolding I_def by auto
      qed (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
           dest: Mapping_keys_dest split: option.splits)
    qed (auto simp add: Mapping_lookup_upd_set valid_tuple_def tuple_since'_def
         intro: Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_prev)"]
        False lookup_tuple_since' ts_tuple_rel_auxlist' table_in' table_since' wf_data_prev'
        valid_before
      unfolding add_def auxlist'_def[symmetric] cur_nt I_def n_def R_def
        valid_mmsaux.simps newest_tuple_in_mapping_def
      by (fastforce simp: lin_data_prev') (* SLOW *)
  qed
qed

lemma valid_add_new_table_mmsaux:
  assumes valid_before: "valid_mmsaux args cur aux auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X aux)
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
  using valid_add_new_table_mmsaux_unfolded assms
  by (cases aux) fast

lemma foldr_ts_tuple_rel:
  "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {} \<longleftrightarrow>
  (\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t)"
proof (rule iffI)
  assume assm: "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {}"
  then obtain t X where tX_def: "P t" "as \<in> X" "(t, X) \<in> set auxlist"
    by (auto elim!: in_foldr_UnE)
  then show "\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t"
    by (auto simp add: ts_tuple_rel_f_def)
next
  assume assm: "\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t"
  then obtain t X where tX_def: "P t" "as \<in> X" "(t, X) \<in> set auxlist"
    by (auto simp add: ts_tuple_rel_f_def)
  show "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {}"
    using in_foldr_UnI[OF tX_def(2)] tX_def assm by (induction auxlist) force+
qed

lemma image_snd: "(a, b) \<in> X \<Longrightarrow> b \<in> snd ` X"
  by force

fun result_mmsaux :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a table" where
  "result_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    Mapping.keys tuple_in"

lemma valid_result_mmsaux_unfolded:
  assumes "valid_mmsaux args cur
    (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  shows "result_mmsaux args (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
  using valid_mmsaux_tuple_in_keys[OF assms] assms
  by (auto simp add: image_Un ts_tuple_rel_Un foldr_ts_tuple_rel image_snd)
     (fastforce intro: ts_tuple_rel_intro dest: ts_tuple_rel_dest)+

lemma valid_result_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  result_mmsaux args aux = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
  using valid_result_mmsaux_unfolded by (cases aux) fast

interpretation default_msaux: msaux valid_mmsaux init_mmsaux add_new_ts_mmsaux gc_join_mmsaux
  add_new_table_mmsaux result_mmsaux
  using valid_init_mmsaux valid_add_new_ts_mmsaux valid_gc_join_mmsaux valid_add_new_table_mmsaux
    valid_result_mmsaux
  by unfold_locales assumption+

subsection \<open>Optimized data structure for Until\<close>

type_synonym tp = nat

type_synonym 'a mmuaux = "tp \<times> ts queue \<times> nat \<times> bool list \<times> bool list \<times>
  ('a tuple, tp) mapping \<times> (tp, ('a tuple, ts + tp) mapping) mapping \<times> 'a table list \<times> nat"

definition tstp_lt :: "ts + tp \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> bool" where
  "tstp_lt tstp ts tp = case_sum (\<lambda>ts'. ts' \<le> ts) (\<lambda>tp'. tp' < tp) tstp"

definition ts_tp_lt :: " \<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> ts + tp \<Rightarrow> bool" where
  "ts_tp_lt I ts tp tstp = case_sum (\<lambda>ts'. memL I (ts' - ts)) (\<lambda>tp'. tp \<le> tp') tstp"

fun max_tstp :: "ts + tp \<Rightarrow> ts + tp \<Rightarrow> ts + tp" where
  "max_tstp (Inl ts) (Inl ts') = Inl (max ts ts')"
| "max_tstp (Inr tp) (Inr tp') = Inr (max tp tp')"
| "max_tstp (Inl ts) _ = Inl ts"
| "max_tstp _ (Inl ts) = Inl ts"

lemma max_tstp_idem: "max_tstp (max_tstp x y) y = max_tstp x y"
  by (cases x; cases y) auto

lemma max_tstp_idem': "max_tstp x (max_tstp x y) = max_tstp x y"
  by (cases x; cases y) auto

lemma max_tstp_d_d: "max_tstp d d = d"
  by (cases d) auto

lemma max_cases: "(max a b = a \<Longrightarrow> P) \<Longrightarrow> (max a b = b \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis max_def)

lemma max_tstpE: "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow> (max_tstp tstp tstp' = tstp \<Longrightarrow> P) \<Longrightarrow>
  (max_tstp tstp tstp' = tstp' \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases tstp; cases tstp') (auto elim: max_cases)

lemma max_tstp_intro: "tstp_lt tstp ts tp \<Longrightarrow> tstp_lt tstp' ts tp \<Longrightarrow> isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  tstp_lt (max_tstp tstp tstp') ts tp"
  by (auto simp add: tstp_lt_def max_def split: sum.splits)

lemma max_tstp_intro': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_lt I ts' tp' tstp \<Longrightarrow> ts_tp_lt I ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto 0 3 simp add: ts_tp_lt_def max_def split: sum.splits)

lemma max_tstp_intro'': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_lt I ts' tp' tstp' \<Longrightarrow> ts_tp_lt I ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto 0 3 simp add: ts_tp_lt_def max_def elim: contrapos_np split: sum.splits)

lemma max_tstp_isl: "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow> isl (max_tstp tstp tstp') \<longleftrightarrow> isl tstp"
  by (cases tstp; cases tstp') auto

definition filter_a1_map :: "bool \<Rightarrow> tp \<Rightarrow> ('a tuple, tp) mapping \<Rightarrow> 'a table" where
  "filter_a1_map pos tp a1_map =
    {xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow>
    (pos \<longrightarrow> tp' \<le> tp) \<and> (\<not>pos \<longrightarrow> tp \<le> tp')}"

definition filter_a2_map :: "\<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow>
  'a table" where
  "filter_a2_map I ts tp a2_map = {xs. \<exists>tp' \<le> tp. (case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
    (case Mapping.lookup m xs of Some tstp \<Rightarrow> ts_tp_lt I ts tp tstp | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)}"

fun triple_eq_pair :: "('a \<times> 'b \<times> 'c) \<Rightarrow> ('a \<times> 'd) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'd \<Rightarrow> 'c) \<Rightarrow> bool" where
  "triple_eq_pair (t, a1, a2) (ts', tp') f g \<longleftrightarrow> t = ts' \<and> a1 = f tp' \<and> a2 = g ts' tp'"

fun valid_mmuaux' :: "args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a muaux \<Rightarrow> bool" where
  "valid_mmuaux' args cur dt (tp, tss, len, maskL, maskR, a1_map, a2_map,
    done, done_length) auxlist \<longleftrightarrow>
    args_L args \<subseteq> args_R args \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    len \<le> tp \<and>
    length (linearize tss) = len \<and> sorted (linearize tss) \<and>
    (\<forall>t \<in> set (linearize tss). t \<le> cur \<and> memR (args_ivl args) (cur - t)) \<and>
    table (args_n args) (args_L args) (Mapping.keys a1_map) \<and>
    Mapping.keys a2_map = {tp - len..tp} \<and>
    (\<forall>xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow> tp' < tp) \<and>
    (\<forall>tp' \<in> Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
      table (args_n args) (args_R args) (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL (args_ivl args) 0))) \<and>
    length done = done_length \<and> length done + len = length auxlist \<and>
    rev done = map proj_thd (take (length done) auxlist) \<and>
    (\<forall>x \<in> set (take (length done) auxlist). check_before (args_ivl args) dt x) \<and>
    sorted (map fst auxlist) \<and>
    list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map (args_pos args) tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map (args_ivl args) ts' tp' a2_map)) (drop (length done) auxlist)
      (zip (linearize tss) [tp - len..<tp])"

definition valid_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a muaux \<Rightarrow>
  bool" where
  "valid_mmuaux args cur = valid_mmuaux' args cur cur"

fun eval_step_mmuaux :: "args \<Rightarrow> 'a mmuaux \<Rightarrow> 'a mmuaux" where
  "eval_step_mmuaux args (tp, tss, len, maskL, maskR, a1_map, a2_map,
    done, done_length) = (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow>
        let m = Mapping.filter (\<lambda>_ tstp. ts_tp_lt (args_ivl args) ts (tp - len) tstp) m;
        T = Mapping.keys m;
        a2_map = Mapping.update (tp - len + 1)
          (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow>
          Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m m') a2_map;
        a2_map = Mapping.delete (tp - len) a2_map in
        (tp, tl_queue tss', len - 1, maskL, maskR, a1_map, a2_map,
        T # done, done_length + 1)))"

lemma Mapping_update_keys: "Mapping.keys (Mapping.update a b m) = Mapping.keys m \<union> {a}"
  by transfer auto

lemma drop_is_Cons_take: "drop n xs = y # ys \<Longrightarrow> take (Suc n) xs = take n xs @ [y]"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases n) simp_all
qed

lemma list_all2_weaken: "list_all2 f xs ys \<Longrightarrow>
  (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x y \<Longrightarrow> f' x y) \<Longrightarrow> list_all2 f' xs ys"
  by (induction xs ys rule: list_all2_induct) auto

lemma Mapping_lookup_delete: "Mapping.lookup (Mapping.delete k m) k' =
  (if k = k' then None else Mapping.lookup m k')"
  by transfer auto

lemma Mapping_lookup_update: "Mapping.lookup (Mapping.update k v m) k' =
  (if k = k' then Some v else Mapping.lookup m k')"
  by transfer auto

lemma hd_le_set: "sorted xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<in> set xs \<Longrightarrow> hd xs \<le> x"
  by (metis eq_iff list.sel(1) set_ConsD sorted.elims(2))

lemma Mapping_lookup_combineE: "Mapping.lookup (Mapping.combine f m m') k = Some v \<Longrightarrow>
  (Mapping.lookup m k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (Mapping.lookup m' k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (\<And>v' v''. Mapping.lookup m k = Some v' \<Longrightarrow> Mapping.lookup m' k = Some v'' \<Longrightarrow>
  f v' v'' = v \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding Mapping.lookup_combine
  by (auto simp add: combine_options_def split: option.splits)

lemma Mapping_keys_filterI: "Mapping.lookup m k = Some v \<Longrightarrow> f k v \<Longrightarrow>
  k \<in> Mapping.keys (Mapping.filter f m)"
  by transfer (auto split: option.splits if_splits)

lemma Mapping_keys_filterD: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  \<exists>v. Mapping.lookup m k = Some v \<and> f k v"
  by transfer (auto split: option.splits if_splits)

fun lin_ts_mmuaux :: "'a mmuaux \<Rightarrow> ts list" where
  "lin_ts_mmuaux (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    linearize tss"

lemma valid_eval_step_mmuaux':
  assumes "valid_mmuaux' args cur dt aux auxlist"
    "lin_ts_mmuaux aux = ts # tss''" "\<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmuaux' args cur dt (eval_step_mmuaux args aux) auxlist \<and>
    lin_ts_mmuaux (eval_step_mmuaux args aux) = tss''"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where aux_def:
    "aux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases aux) auto
  then obtain tss' where safe_hd_eq: "safe_hd tss = (Some ts, tss')"
    using assms(2) safe_hd_rep case_optionE
    by (cases "safe_hd tss") fastforce
  note valid_before = assms(1)[unfolded aux_def]
  have lin_tss_not_Nil: "linearize tss \<noteq> []"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have ts_hd: "ts = hd (linearize tss)"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have lin_tss': "linearize tss' = linearize tss"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have tss'_not_empty: "\<not>is_empty tss'"
    using is_empty_alt[of tss'] lin_tss_not_Nil unfolding lin_tss' by auto
  have len_pos: "len > 0"
    using lin_tss_not_Nil valid_before by auto
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using valid_before by auto
  have len_tp: "len \<le> tp"
    using valid_before by auto
  have tp_minus_keys: "tp - len \<in> Mapping.keys a2_map"
    using a2_map_keys by auto
  have tp_minus_keys': "tp - len + 1 \<in> Mapping.keys a2_map"
    using a2_map_keys len_pos len_tp by auto
  obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
    using tp_minus_keys by (auto dest: Mapping_keys_dest)
  have "table n R (Mapping.keys m)"
    "(\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using tp_minus_keys m_def valid_before
    unfolding valid_mmuaux'.simps n_def I_def R_def by fastforce+
  then have m_inst: "table n R (Mapping.keys m)"
    "\<And>xs tstp. Mapping.lookup m xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    using Mapping_keys_intro by fastforce+
  have m_inst_isl: "\<And>xs tstp. Mapping.lookup m xs = Some tstp \<Longrightarrow> isl tstp \<longleftrightarrow> \<not> memL I 0"
    using m_inst(2) by fastforce
  obtain m' where m'_def: "Mapping.lookup a2_map (tp - len + 1) = Some m'"
    using tp_minus_keys' by (auto dest: Mapping_keys_dest)
  have "table n R (Mapping.keys m')"
    "(\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using tp_minus_keys' m'_def valid_before
    unfolding valid_mmuaux'.simps I_def n_def R_def by fastforce+
  then have m'_inst: "table n R (Mapping.keys m')"
    "\<And>xs tstp. Mapping.lookup m' xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    using Mapping_keys_intro by fastforce+
  have m'_inst_isl: "\<And>xs tstp. Mapping.lookup m' xs = Some tstp \<Longrightarrow> isl tstp \<longleftrightarrow> \<not> memL I 0"
    using m'_inst(2) by fastforce
  define m_upd where "m_upd = Mapping.filter (\<lambda>_ tstp. ts_tp_lt I ts (tp - len) tstp) m"
  define T where "T = Mapping.keys m_upd"
  define mc where "mc = Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m_upd m'"
  define a2_map' where "a2_map' = Mapping.update (tp - len + 1) mc a2_map"
  define a2_map'' where "a2_map'' = Mapping.delete (tp - len) a2_map'"
  have m_upd_lookup: "\<And>xs tstp. Mapping.lookup m_upd xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    unfolding m_upd_def Mapping.lookup_filter
    using m_inst(2) by (auto split: option.splits if_splits)
  have mc_lookup: "\<And>xs tstp. Mapping.lookup mc xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    unfolding mc_def Mapping.lookup_combine
    using m_upd_lookup m'_inst(2)
    by (auto simp add: combine_options_def max_tstp_isl intro: max_tstp_intro split: option.splits)
  have mc_keys: "Mapping.keys mc \<subseteq> Mapping.keys m \<union> Mapping.keys m'"
    unfolding mc_def Mapping.keys_combine m_upd_def
    using Mapping.keys_filter by fastforce
  have tp_len_assoc: "tp - len + 1 = tp - (len - 1)"
    using len_pos len_tp by auto
  have a2_map''_keys: "Mapping.keys a2_map'' = {tp - (len - 1)..tp}"
    unfolding a2_map''_def a2_map'_def Mapping.keys_delete Mapping_update_keys a2_map_keys
    using tp_len_assoc by auto
  have lin_tss_Cons: "linearize tss = ts # linearize (tl_queue tss')"
    using lin_tss_not_Nil
    by (auto simp add: tl_queue_rep[OF tss'_not_empty] lin_tss' ts_hd)
  have tp_len_tp_unfold: "[tp - len..<tp] = (tp - len) # [tp - (len - 1)..<tp]"
    unfolding tp_len_assoc[symmetric]
    using len_pos len_tp Suc_diff_le upt_conv_Cons by auto
  have id: "\<And>x. x \<in> {tp - (len - 1) + 1..tp} \<Longrightarrow>
    Mapping.lookup a2_map'' x = Mapping.lookup a2_map x"
    unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update tp_len_assoc
    using len_tp by auto
  have list_all2: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map))
    (drop (length done) auxlist) (zip (linearize tss) [tp - len..<tp])"
    using valid_before unfolding I_def pos_def by auto
  obtain hd_aux tl_aux where aux_split: "drop (length done) auxlist = hd_aux # tl_aux"
    "case hd_aux of (t, a1, a2) \<Rightarrow> (t, a1, a2) =
    (ts, filter_a1_map pos (tp - len) a1_map, filter_a2_map I ts (tp - len) a2_map)"
    and list_all2': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)) tl_aux
      (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])"
    using list_all2[unfolded lin_tss_Cons tp_len_tp_unfold zip_Cons_Cons list_all2_Cons2] by auto
  have lookup''_tp_minus: "Mapping.lookup a2_map'' (tp - (len - 1)) = Some mc"
    unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update
      tp_len_assoc[symmetric]
    using len_tp by auto
  have filter_a2_map_cong: "\<And>ts' tp'. ts' \<in> set (linearize tss) \<Longrightarrow>
    tp' \<in> {tp - (len - 1)..<tp} \<Longrightarrow> filter_a2_map I ts' tp' a2_map =
    filter_a2_map I ts' tp' a2_map''"
  proof (rule set_eqI, rule iffI)
    fix ts' tp' xs
    assume assms: "ts' \<in> set (linearize tss)"
      "tp' \<in> {tp - (len - 1)..<tp}" "xs \<in> filter_a2_map I ts' tp' a2_map"
    obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp'" "Mapping.lookup a2_map tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      using assms(3)[unfolded filter_a2_map_def]
      by (fastforce split: option.splits)
    have ts_le_ts': "ts \<le> ts'"
      using hd_le_set[OF _ lin_tss_not_Nil assms(1)] valid_before
      unfolding ts_hd by auto
    have tp_bef_in: "tp_bef \<in> {tp - len..tp}"
      using defs(2) valid_before by (auto intro!: Mapping_keys_intro)
    have tp_minus_le: "tp - (len - 1) \<le> tp'"
      using assms(2) by auto
    show "xs \<in> filter_a2_map I ts' tp' a2_map''"
    proof (cases "tp_bef \<le> tp - (len - 1)")
      case True
      show ?thesis
      proof (cases "tp_bef = tp - len")
        case True
        have m_bef_m: "m_bef = m"
          using defs(2) m_def
          unfolding True by auto
        have "Mapping.lookup m_upd xs = Some tstp"
          using defs(3,4) assms(2) ts_le_ts' unfolding m_bef_m m_upd_def
          by (auto 0 3 simp add: Mapping.lookup_filter ts_tp_lt_def intro: Mapping_keys_intro
              split: sum.splits elim: contrapos_np)
        then have "case Mapping.lookup mc xs of None \<Rightarrow> False | Some tstp \<Rightarrow>
          ts_tp_lt I ts' tp' tstp"
          unfolding mc_def Mapping.lookup_combine
          using m'_inst(2) m_upd_lookup
          by (auto simp add: combine_options_def defs(4) intro!: max_tstp_intro'
              dest: Mapping_keys_dest split: option.splits)
        then show ?thesis
          using lookup''_tp_minus tp_minus_le defs
          unfolding m_bef_m filter_a2_map_def by (auto split: option.splits)
      next
        case False
        then have "tp_bef = tp - (len - 1)"
          using True tp_bef_in by auto
        then have m_bef_m: "m_bef = m'"
          using defs(2) m'_def
          unfolding tp_len_assoc by auto
        have "case Mapping.lookup mc xs of None \<Rightarrow> False | Some tstp \<Rightarrow>
          ts_tp_lt I ts' tp' tstp"
          unfolding mc_def Mapping.lookup_combine
          using m'_inst(2) m_upd_lookup defs(3)[unfolded m_bef_m]
          by (auto simp add: combine_options_def defs(4) intro!: max_tstp_intro''
              dest: Mapping_keys_dest split: option.splits)
        then show ?thesis
          using lookup''_tp_minus tp_minus_le defs
          unfolding m_bef_m filter_a2_map_def by (auto split: option.splits)
      qed
    next
      case False
      then have "Mapping.lookup a2_map'' tp_bef = Mapping.lookup a2_map tp_bef"
        using id tp_bef_in len_tp by auto
      then show ?thesis
        unfolding filter_a2_map_def
        using defs by auto
    qed
  next
    fix ts' tp' xs
    assume assms: "ts' \<in> set (linearize tss)" "tp' \<in> {tp - (len - 1)..<tp}"
      "xs \<in> filter_a2_map I ts' tp' a2_map''"
    obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp'"
      "Mapping.lookup a2_map'' tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      using assms(3)[unfolded filter_a2_map_def]
      by (fastforce split: option.splits)
    have ts_le_ts': "ts \<le> ts'"
      using hd_le_set[OF _ lin_tss_not_Nil assms(1)] valid_before
      unfolding ts_hd by auto
    have tp_bef_in: "tp_bef \<in> {tp - (len - 1)..tp}"
      using defs(2) a2_map''_keys by (auto intro!: Mapping_keys_intro)
    have tp_minus_le: "tp - len \<le> tp'" "tp - (len - 1) \<le> tp'"
      using assms(2) by auto
    show "xs \<in> filter_a2_map I ts' tp' a2_map"
    proof (cases "tp_bef = tp - (len - 1)")
      case True
      have m_beg_mc: "m_bef = mc"
        using defs(2)
        unfolding True a2_map''_def a2_map'_def tp_len_assoc Mapping_lookup_delete
          Mapping.lookup_update
        by (auto split: if_splits)
      show ?thesis
        using defs(3)[unfolded m_beg_mc mc_def]
      proof (rule Mapping_lookup_combineE)
        assume lassm: "Mapping.lookup m_upd xs = Some tstp"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map"
          unfolding m_upd_def Mapping.lookup_filter
          using m_def tp_minus_le(1) defs
          by (auto simp add: filter_a2_map_def split: option.splits if_splits)
      next
        assume lassm: "Mapping.lookup m' xs = Some tstp"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map"
          using m'_def defs(4) tp_minus_le defs
          unfolding filter_a2_map_def tp_len_assoc
          by auto
      next
        fix v' v''
        assume lassms: "Mapping.lookup m_upd xs = Some v'" "Mapping.lookup m' xs = Some v''"
          "max_tstp v' v'' = tstp"
        show "xs \<in> filter_a2_map I ts' tp' a2_map"
        proof (rule max_tstpE)
          show "isl v' = isl v''"
            using lassms(1,2) m_upd_lookup m'_inst(2)
            by auto
        next
          assume "max_tstp v' v'' = v'"
          then show "xs \<in> filter_a2_map I ts' tp' a2_map"
            using lassms(1,3) m_def defs tp_minus_le(1)
            unfolding tp_len_assoc m_upd_def Mapping.lookup_filter
            by (auto simp add: filter_a2_map_def split: option.splits if_splits)
        next
          assume "max_tstp v' v'' = v''"
          then show "xs \<in> filter_a2_map I ts' tp' a2_map"
            using lassms(2,3) m'_def defs tp_minus_le(2)
            unfolding tp_len_assoc
            by (auto simp add: filter_a2_map_def)
        qed
      qed
    next
      case False
      then have "Mapping.lookup a2_map'' tp_bef = Mapping.lookup a2_map tp_bef"
        using id tp_bef_in by auto
      then show ?thesis
        unfolding filter_a2_map_def
        using defs by auto (metis option.simps(5))
    qed
  qed
  have set_tl_tss': "set (linearize (tl_queue tss')) \<subseteq> set (linearize tss)"
    unfolding tl_queue_rep[OF tss'_not_empty] lin_tss_Cons by auto
  have list_all2'': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'')) tl_aux
      (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])"
    using filter_a2_map_cong set_tl_tss'
    by (intro list_all2_weaken[OF list_all2']) (auto elim!: in_set_zipE split: prod.splits)
  have lookup'': "\<forall>tp' \<in> Mapping.keys a2_map''. case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
    table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
  proof (rule ballI)
    fix tp'
    assume assm: "tp' \<in> Mapping.keys a2_map''"
    then obtain f where f_def: "Mapping.lookup a2_map'' tp' = Some f"
      by (auto dest: Mapping_keys_dest)
    have tp'_in: "tp' \<in> {tp - (len - 1)..tp}"
      using assm unfolding a2_map''_keys .
    then have tp'_in_keys: "tp' \<in> Mapping.keys a2_map"
      using valid_before by auto
    have "table n R (Mapping.keys f) \<and>
      (\<forall>xs \<in> Mapping.keys f. case Mapping.lookup f xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
    proof (cases "tp' = tp - (len - 1)")
      case True
      then have f_mc: "f = mc"
        using f_def
        unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update tp_len_assoc
        by (auto split: if_splits)
      have "table n R (Mapping.keys f)"
        unfolding f_mc
        using mc_keys m_def m'_def m_inst m'_inst
        by (auto simp add: table_def)
      moreover have "\<forall>xs \<in> Mapping.keys f. case Mapping.lookup f xs of Some tstp \<Rightarrow>
        tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0)"
        using assm Mapping.keys_filter m_inst(2) m_inst_isl m'_inst(2) m'_inst_isl max_tstp_isl
        unfolding f_mc mc_def Mapping.lookup_combine
        by (auto simp add: combine_options_def m_upd_def Mapping.lookup_filter
            intro!: max_tstp_intro Mapping_keys_intro dest!: Mapping_keys_dest
            split: option.splits)
      ultimately show ?thesis
        by auto
    next
      case False
      have "Mapping.lookup a2_map tp' = Some f"
        using tp'_in id[of tp'] f_def False by auto
      then show ?thesis
        using tp'_in_keys valid_before
        unfolding valid_mmuaux'.simps I_def n_def R_def by fastforce
    qed
    then show "case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
      table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
      using f_def by auto
  qed
  have tl_aux_def: "tl_aux = drop (length done + 1) auxlist"
    using aux_split(1) by (metis Suc_eq_plus1 add_Suc drop0 drop_Suc_Cons drop_drop)
  have T_eq: "T = filter_a2_map I ts (tp - len) a2_map"
  proof (rule set_eqI, rule iffI)
    fix xs
    assume "xs \<in> filter_a2_map I ts (tp - len) a2_map"
    then obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp - len"
      "Mapping.lookup a2_map tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts (tp - len) tstp"
      by (fastforce simp add: filter_a2_map_def split: option.splits)
    then have tp_bef_minus: "tp_bef = tp - len"
      using valid_before Mapping_keys_intro by force
    have m_bef_m: "m_bef = m"
      using defs(2) m_def
      unfolding tp_bef_minus by auto
    show "xs \<in> T"
      using defs
      unfolding T_def m_upd_def m_bef_m
      by (auto intro: Mapping_keys_filterI Mapping_keys_intro)
  next
    fix xs
    assume "xs \<in> T"
    then show "xs \<in> filter_a2_map I ts (tp - len) a2_map"
      using m_def Mapping.keys_filter
      unfolding T_def m_upd_def filter_a2_map_def
      by (auto simp add: filter_a2_map_def dest!: Mapping_keys_filterD split: if_splits)
  qed
  have min_auxlist_done: "min (length auxlist) (length done) = length done"
    using valid_before by auto
  then have "\<forall>x \<in> set (take (length done) auxlist). check_before I dt x"
    "rev done = map proj_thd (take (length done) auxlist)"
    using valid_before unfolding I_def by auto
  then have list_all': "(\<forall>x \<in> set (take (length (T # done)) auxlist). check_before I dt x)"
    "rev (T # done) = map proj_thd (take (length (T # done)) auxlist)"
    using drop_is_Cons_take[OF aux_split(1)] aux_split(2) assms(3)
    by (auto simp add: T_eq I_def)
  have eval_step_mmuaux_eq: "eval_step_mmuaux args (tp, tss, len, maskL, maskR, a1_map, a2_map,
    done, done_length) = (tp, tl_queue tss', len - 1,  maskL, maskR, a1_map, a2_map'',
    T # done, done_length + 1)"
    using safe_hd_eq m_def m'_def m_upd_def T_def mc_def a2_map'_def a2_map''_def I_def
    by (auto simp add: Let_def)
  have "lin_ts_mmuaux (eval_step_mmuaux args aux) = tss''"
    using lin_tss_Cons assms(2) unfolding aux_def eval_step_mmuaux_eq by auto
  then show ?thesis
    using valid_before a2_map''_keys sorted_tl list_all' lookup'' list_all2''
    unfolding eval_step_mmuaux_eq valid_mmuaux'.simps tl_aux_def aux_def I_def n_def R_def pos_def
    using lin_tss_not_Nil safe_hd_eq len_pos
    by (auto simp add: list.set_sel(2) lin_tss' tl_queue_rep[OF tss'_not_empty] min_auxlist_done)
qed

lemma done_empty_valid_mmuaux'_intro:
  assumes "valid_mmuaux' args cur dt
    (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) auxlist"
  shows "valid_mmuaux' args cur dt'
    (tp, tss, len, maskL, maskR, a1_map, a2_map, [], 0)
    (drop (length done) auxlist)"
  using assms sorted_drop by (auto simp add: drop_map[symmetric])

lemma valid_mmuaux'_mono:
  assumes "valid_mmuaux' args cur dt aux auxlist" "dt \<le> dt'"
  shows "valid_mmuaux' args cur dt' aux auxlist"
  using assms less_le_trans by (cases aux) (fastforce simp: memR_antimono)

lemma valid_foldl_eval_step_mmuaux':
  assumes valid_before: "valid_mmuaux' args cur dt aux auxlist"
    "lin_ts_mmuaux aux = tss @ tss'"
    "\<And>ts. ts \<in> set (take (length tss) (lin_ts_mmuaux aux)) \<Longrightarrow> \<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmuaux' args cur dt (foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss) auxlist \<and>
    lin_ts_mmuaux (foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss) = tss'"
  using assms
proof (induction tss arbitrary: aux)
  case (Cons ts tss)
  have app_ass: "lin_ts_mmuaux aux = ts # (tss @ tss')"
    using Cons(3) by auto
  have "\<not> memR (args_ivl args) (dt - ts)"
    using Cons by auto
  then have valid_step: "valid_mmuaux' args cur dt (eval_step_mmuaux args aux) auxlist"
    "lin_ts_mmuaux (eval_step_mmuaux args aux) = tss @ tss'"
    using valid_eval_step_mmuaux'[OF Cons(2) app_ass] by auto
  show ?case
    using Cons(1)[OF valid_step] valid_step Cons(4) app_ass by auto
qed auto

lemma sorted_dropWhile_filter: "sorted xs \<Longrightarrow> dropWhile (\<lambda>t. \<not> memR I (nt - t)) xs =
  filter (\<lambda>t. memR I (nt - t)) xs"
proof (induction xs)
  case (Cons x xs)
  then show ?case
  proof (cases "\<not> memR I (nt - x)")
    case False
    then have neg: "memR I (nt - x)"
      by auto
    with Cons have "\<And>z. z \<in> set xs \<Longrightarrow> memR I (nt - z)"
      by (auto simp: diff_le_mono2)
    with False show ?thesis
      using filter_empty_conv by auto
  qed auto
qed auto

fun shift_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a mmuaux" where
  "shift_mmuaux args nt (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    (let tss_list = linearize (takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss) in
    foldl (\<lambda>aux _. eval_step_mmuaux args aux) (tp, tss, len, maskL, maskR,
      a1_map, a2_map, done, done_length) tss_list)"

lemma valid_shift_mmuaux':
  assumes "valid_mmuaux' args cur cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmuaux' args cur nt (shift_mmuaux args nt aux) auxlist \<and>
    (\<forall>ts \<in> set (lin_ts_mmuaux (shift_mmuaux args nt aux)). memR (args_ivl args) (nt - ts))"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,2) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where aux_def:
    "aux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases aux) auto
  note valid_before = valid_folded[unfolded aux_def]
  define tss_list where "tss_list =
    linearize (takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss)"
  have tss_list_takeWhile: "tss_list = takeWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    using tss_list_def unfolding takeWhile_queue_rep .
  then obtain tss_list' where tss_list'_def: "linearize tss = tss_list @ tss_list'"
    "tss_list' = dropWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    by auto
  obtain tp' len' tss' maskL' maskR' a1_map' a2_map' "done'" done_length' where
    foldl_aux_def: "(tp', tss', len', maskL', maskR', a1_map', a2_map',
      done', done_length') = foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss_list"
    by (cases "foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss_list") auto
  have lin_tss_aux: "lin_ts_mmuaux aux = linearize tss"
    unfolding aux_def by auto
  have "take (length tss_list) (lin_ts_mmuaux aux) = tss_list"
    unfolding lin_tss_aux using tss_list'_def(1) by auto
  then have valid_foldl: "valid_mmuaux' args cur nt
    (foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss_list) auxlist"
    "lin_ts_mmuaux (foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss_list) = tss_list'"
    using valid_foldl_eval_step_mmuaux'[OF valid_before[folded aux_def], unfolded lin_tss_aux,
      OF tss_list'_def(1)] tss_list_takeWhile set_takeWhileD
    unfolding lin_tss_aux I_def by fastforce+
  have shift_mmuaux_eq: "shift_mmuaux args nt aux = foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss_list"
    using tss_list_def unfolding aux_def I_def by auto
  have "\<And>ts. ts \<in> set tss_list' \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using sorted_dropWhile_filter tss_list'_def(2) valid_before unfolding I_def by auto
  then show ?thesis
    using valid_foldl(1)[unfolded shift_mmuaux_eq[symmetric]]
    unfolding valid_foldl(2)[unfolded shift_mmuaux_eq[symmetric]] by auto
qed

lift_definition upd_set' :: "('a, 'b) mapping \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m d f X a. (if a \<in> X then (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d)
    else Mapping.lookup m a)" .

lemma upd_set'_lookup: "Mapping.lookup (upd_set' m d f X) a = (if a \<in> X then
  (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set'.rep_eq)

lemma upd_set'_keys: "Mapping.keys (upd_set' m d f X) = Mapping.keys m \<union> X"
  by (auto simp add: upd_set'_lookup intro!: Mapping_keys_intro
      dest!: Mapping_keys_dest split: option.splits)

lift_definition upd_nested :: "('a, ('b, 'c) mapping) mapping \<Rightarrow>
  'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a, ('b, 'c) mapping) mapping" is
  "\<lambda>m d f X a. case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None" .

lemma upd_nested_lookup: "Mapping.lookup (upd_nested m d f X) a =
  (case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None)"
  by (simp add: Mapping.lookup.abs_eq upd_nested.abs_eq)

lemma upd_nested_keys: "Mapping.keys (upd_nested m d f X) = Mapping.keys m \<union> fst ` X"
  by (auto simp add: upd_nested_lookup Domain.DomainI fst_eq_Domain intro!: Mapping_keys_intro
      dest!: Mapping_keys_dest split: option.splits)

fun add_new_mmuaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a mmuaux" where
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, len + 1, maskL, maskR, a1_map, a2_map, done, done_length))"

lemma fst_case: "(\<lambda>x. fst (case x of (t, a1, a2) \<Rightarrow> (t, y t a1 a2, z t a1 a2))) = fst"
  by auto

lemma list_all2_in_setE: "list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> (\<And>y. y \<in> set ys \<Longrightarrow> P x y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fastforce simp: list_all2_iff set_zip in_set_conv_nth)

lemma list_all2_zip: "list_all2 (\<lambda>x y. triple_eq_pair x y f g) xs (zip ys zs) \<Longrightarrow>
  (\<And>y. y \<in> set ys \<Longrightarrow> Q y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> Q (fst x)"
  by (auto simp: in_set_zip elim!: list_all2_in_setE triple_eq_pair.elims)

lemma list_appendE: "xs = ys @ zs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
  (x \<in> set ys \<Longrightarrow> P) \<Longrightarrow> (x \<in> set zs \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma take_takeWhile: "n \<le> length ys \<Longrightarrow>
  (\<And>y. y \<in> set (take n ys) \<Longrightarrow> P y) \<Longrightarrow>
  (\<And>y. y \<in> set (drop n ys) \<Longrightarrow> \<not>P y) \<Longrightarrow>
  take n ys = takeWhile P ys"
proof (induction ys arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases n) simp_all
qed

lemma valid_add_new_mmuaux:
  assumes valid_before: "valid_mmuaux args cur aux auxlist"
    and tabs: "table (args_n args) (args_L args) rel1" "table (args_n args) (args_R args) rel2"
    and nt_mono: "nt \<ge> cur"
  shows "valid_mmuaux args nt (add_new_mmuaux args rel1 rel2 nt aux)
    (update_until args rel1 rel2 nt auxlist)"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,4) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where shift_aux_def:
    "shift_mmuaux args nt aux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases "shift_mmuaux args nt aux") auto
  have valid_shift_aux: "valid_mmuaux' args cur nt (tp, tss, len, maskL, maskR,
    a1_map, a2_map, done, done_length) auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using valid_shift_mmuaux'[OF assms(1)[unfolded valid_mmuaux_def] assms(4)]
    unfolding shift_aux_def by auto
  define new_tstp where "new_tstp = (if memL I 0 then Inr tp else Inl nt)"
  have new_tstp_lt_isl: "tstp_lt new_tstp nt (tp + 1)"
    "isl new_tstp \<longleftrightarrow> \<not> memL I 0"
    by (auto simp add: new_tstp_def tstp_lt_def)
  define tmp where "tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
    (if \<not>pos then {(tp - len, as)} else {})
    | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
    else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {})"
  have a1_map_lookup: "\<And>as tp'. Mapping.lookup a1_map as = Some tp' \<Longrightarrow> tp' < tp"
    using valid_shift_aux(1) Mapping_keys_intro by force
  then have fst_tmp: "\<And>tp'. tp' \<in> fst ` tmp \<Longrightarrow> tp - len \<le> tp' \<and> tp' < tp + 1"
    unfolding tmp_def by (auto simp add: less_SucI split: option.splits if_splits)
  have snd_tmp: "\<And>tp'. table n R (snd ` tmp)"
    using tabs(2) unfolding tmp_def n_def R_def
    by (auto simp add: table_def split: if_splits option.splits)
  define a2_map' where "a2_map' = Mapping.update (tp + 1) Mapping.empty
    (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp)"
  define a1_map' where "a1_map' = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
    (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1)"
  define tss' where "tss' = append_queue nt tss"
  have add_new_mmuaux_eq: "add_new_mmuaux args rel1 rel2 nt aux = (tp + 1, tss', len + 1,
    maskL, maskR, a1_map', a2_map', done, done_length)"
    using shift_aux_def new_tstp_def tmp_def a2_map'_def a1_map'_def tss'_def
    unfolding I_def pos_def
    by (auto simp only: add_new_mmuaux.simps Let_def)
  have update_until_eq: "update_until args rel1 rel2 nt auxlist =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) auxlist) @
    [(nt, rel1, if memL I 0 then rel2 else empty_table)]"
    unfolding update_until_def I_def pos_def by simp
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have auxlist_split: "auxlist = take (length done) auxlist @ drop (length done) auxlist"
    using len_done_auxlist by auto
  have lin_tss': "linearize tss' = linearize tss @ [nt]"
    unfolding tss'_def append_queue_rep by (rule refl)
  have len_lin_tss': "length (linearize tss') = len + 1"
    unfolding lin_tss' using valid_shift_aux by auto
  have tmp: "sorted (linearize tss)" "\<And>t. t \<in> set (linearize tss) \<Longrightarrow> t \<le> cur"
    using valid_shift_aux by auto
  have sorted_lin_tss': "sorted (linearize tss')"
    unfolding lin_tss' using tmp(1) le_trans[OF _ assms(4), OF tmp(2)]
    by (simp add: sorted_append)
  have in_lin_tss: "\<And>t. t \<in> set (linearize tss) \<Longrightarrow>
    t \<le> cur \<and> memR I (cur - t)"
    using valid_shift_aux(1) unfolding I_def by auto
  then have set_lin_tss': "\<forall>t \<in> set (linearize tss'). t \<le> nt \<and> memR I (nt - t)"
    unfolding lin_tss' I_def using le_trans[OF _ assms(4)] valid_shift_aux(2)
    by (auto simp add: not_less)
  have a1_map'_keys: "Mapping.keys a1_map' \<subseteq> Mapping.keys a1_map \<union> rel1"
    unfolding a1_map'_def using Mapping.keys_filter Mapping_upd_set_keys
    by (auto simp add: Mapping_upd_set_keys split: if_splits dest: Mapping_keys_filterD)
  then have tab_a1_map'_keys: "table n L (Mapping.keys a1_map')"
    using valid_shift_aux(1) tabs(1) by (auto simp add: table_def n_def L_def)
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using valid_shift_aux by auto
  have a2_map'_keys: "Mapping.keys a2_map' = {tp - len..tp + 1}"
    unfolding a2_map'_def Mapping.keys_update upd_nested_keys a2_map_keys using fst_tmp
    by fastforce
  then have a2_map'_keys': "Mapping.keys a2_map' = {tp + 1 - (len + 1)..tp + 1}"
    by auto
  have len_upd_until: "length done + (len + 1) = length (update_until args rel1 rel2 nt auxlist)"
    using valid_shift_aux unfolding update_until_eq by auto
  have set_take_auxlist: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have list_all2_triple: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)) (drop (length done) auxlist)
    (zip (linearize tss) [tp - len..<tp])"
    using valid_shift_aux unfolding I_def pos_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux(2)[OF list_all2_zip[OF list_all2_triple,
      of "\<lambda>y. y \<in> set (linearize tss)"]]
    unfolding I_def by auto
  have length_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using take_takeWhile[OF length_done_auxlist set_take_auxlist set_drop_auxlist] .
  have "length done = length (takeWhile (check_before I nt) auxlist)"
    by (metis (no_types) add_diff_cancel_right' auxlist_split diff_diff_cancel
        length_append length_done_auxlist length_drop take_auxlist_takeWhile)
  then have set_take_auxlist': "\<And>x. x \<in> set (take (length done)
    (update_until args rel1 rel2 nt auxlist)) \<Longrightarrow> check_before I nt x"
    by (metis I_def length_map map_proj_thd_update_until set_takeWhileD takeWhile_eq_take)
  have rev_done: "rev done = map proj_thd (take (length done) auxlist)"
    using valid_shift_aux by auto
  moreover have "\<dots> = map proj_thd (takeWhile (check_before I nt)
    (update_until args rel1 rel2 nt auxlist))"
    by (simp add: take_auxlist_takeWhile map_proj_thd_update_until I_def)
  finally have rev_done': "rev done = map proj_thd (take (length done)
    (update_until args rel1 rel2 nt auxlist))"
    by (metis length_map length_rev takeWhile_eq_take)
  have map_fst_auxlist_take: "\<And>t. t \<in> set (map fst (take (length done) auxlist)) \<Longrightarrow> t \<le> nt"
    using set_take_auxlist linear by fastforce
  have map_fst_auxlist_drop: "\<And>t. t \<in> set (map fst (drop (length done) auxlist)) \<Longrightarrow> t \<le> nt"
    using in_lin_tss[OF list_all2_zip[OF list_all2_triple, of "\<lambda>y. y \<in> set (linearize tss)"]]
      assms(4) dual_order.trans by auto blast
  have set_drop_auxlist_cong: "\<And>x t a1 a2. x \<in> set (drop (length done) auxlist) \<Longrightarrow>
    x = (t, a1, a2) \<Longrightarrow> mem I ((nt - t)) \<longleftrightarrow> memL I (nt - t)"
  proof -
    fix x t a1 a2
    assume "x \<in> set (drop (length done) auxlist)" "x = (t, a1, a2)"
    then have "memR I (nt - t)"
      using set_drop_auxlist not_less
      by auto
    then show "mem I (nt - t) \<longleftrightarrow> memL I (nt - t)"
      by auto
  qed
  have sorted_fst_auxlist: "sorted (map fst auxlist)"
    using valid_shift_aux by auto
  have set_map_fst_auxlist: "\<And>t. t \<in> set (map fst auxlist) \<Longrightarrow> t \<le> nt"
    using arg_cong[OF auxlist_split, of "map fst", unfolded map_append] map_fst_auxlist_take
      map_fst_auxlist_drop by auto
  have lookup_a1_map_keys: "\<And>xs tp'. Mapping.lookup a1_map xs = Some tp' \<Longrightarrow> tp' < tp"
    using valid_shift_aux Mapping_keys_intro by force
  have lookup_a1_map_keys': "\<forall>xs \<in> Mapping.keys a1_map'.
    case Mapping.lookup a1_map' xs of Some tp' \<Rightarrow> tp' < tp + 1"
    using lookup_a1_map_keys unfolding a1_map'_def
    by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set Mapping_upd_set_keys
        split: option.splits dest: Mapping_keys_dest) fastforce+
  have sorted_upd_until: "sorted (map fst (update_until args rel1 rel2 nt auxlist))"
    using sorted_fst_auxlist set_map_fst_auxlist
    unfolding update_until_eq
    by (auto simp add: sorted_append comp_def fst_case)
  have lookup_a2_map: "\<And>tp' m. Mapping.lookup a2_map tp' = Some m \<Longrightarrow>
    table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using valid_shift_aux(1) Mapping_keys_intro unfolding I_def n_def R_def by force
  then have lookup_a2_map': "\<And>tp' m xs tstp. Mapping.lookup a2_map tp' = Some m \<Longrightarrow>
    Mapping.lookup m xs = Some tstp \<Longrightarrow> tstp_lt tstp nt tp \<and>
    isl tstp = (\<not> memL I 0)"
    using Mapping_keys_intro assms(4) by (force simp add: tstp_lt_def split: sum.splits)
  have lookup_a2_map'_keys: "\<forall>tp' \<in> Mapping.keys a2_map'.
    case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> table n R (Mapping.keys m) \<and>
    (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
  proof (rule ballI)
    fix tp'
    assume tp'_assm: "tp' \<in> Mapping.keys a2_map'"
    then obtain m' where m'_def: "Mapping.lookup a2_map' tp' = Some m'"
      by (auto dest: Mapping_keys_dest)
    have "table n R (Mapping.keys m') \<and>
      (\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
      tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
    proof (cases "tp' = tp + 1")
      case True
      show ?thesis
        using m'_def unfolding a2_map'_def True Mapping.lookup_update
        by (auto simp add: table_def)
    next
      case False
      then have tp'_in: "tp' \<in> Mapping.keys a2_map"
        using tp'_assm unfolding a2_map_keys a2_map'_keys by auto
      then obtain m where m_def: "Mapping.lookup a2_map tp' = Some m"
        by (auto dest: Mapping_keys_dest)
      have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp}"
        using m_def m'_def unfolding a2_map'_def Mapping.lookup_update_neq[OF False[symmetric]]
          upd_nested_lookup
        by auto
      have "table n R (Mapping.keys m')"
        using lookup_a2_map[OF m_def] snd_tmp unfolding m'_alt upd_set'_keys
        by (auto simp add: table_def)
      moreover have "\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
        tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
      proof (rule ballI)
        fix xs
        assume xs_assm: "xs \<in> Mapping.keys m'"
        then obtain tstp where tstp_def: "Mapping.lookup m' xs = Some tstp"
          by (auto dest: Mapping_keys_dest)
        have "tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
        proof (cases "Mapping.lookup m xs")
          case None
          then show ?thesis
            using tstp_def[unfolded m'_alt upd_set'_lookup] new_tstp_lt_isl
            by (auto split: if_splits)
        next
          case (Some tstp')
          show ?thesis
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using tstp_def[unfolded m'_alt upd_set'_lookup] Some
              by auto
            show ?thesis
              using lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
              by (auto simp add: tstp_lt_def tstp_eq max_def split: sum.splits)
          next
            case False
            then show ?thesis
              using tstp_def[unfolded m'_alt upd_set'_lookup] lookup_a2_map'[OF m_def Some] Some
              by (auto simp add: tstp_lt_def split: sum.splits)
          qed
        qed
        then show "case Mapping.lookup m' xs of Some tstp \<Rightarrow>
          tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
          using tstp_def by auto
      qed
      ultimately show ?thesis
        by auto
    qed
    then show "case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> table n R (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
      using m'_def by auto
  qed
  have tp_upt_Suc: "[tp + 1 - (len + 1)..<tp + 1] = [tp - len..<tp] @ [tp]"
    using upt_Suc by auto
  have map_eq: "map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist) =
    map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist)"
    using set_drop_auxlist_cong by auto
  have "drop (length done) (update_until args rel1 rel2 nt auxlist) =
    map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist) @
    [(nt, rel1, if memL I 0 then rel2 else empty_table)]"
    unfolding update_until_eq using len_done_auxlist drop_map by auto
  note drop_update_until = this[unfolded map_eq]
  have list_all2_old: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map')
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'))
    (map (\<lambda>(t, a1, a2). (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist))
    (zip (linearize tss) [tp - len..<tp])"
    unfolding list_all2_map1
    using list_all2_triple
  proof (rule list.rel_mono_strong)
    fix tri pair
    assume tri_pair_in: "tri \<in> set (drop (length done) auxlist)"
      "pair \<in> set (zip (linearize tss) [tp - len..<tp])"
    obtain t a1 a2 where tri_def: "tri = (t, a1, a2)"
      by (cases tri) auto
    obtain ts' tp' where pair_def: "pair = (ts', tp')"
      by (cases pair) auto
    assume "triple_eq_pair tri pair (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)"
    then have eqs: "t = ts'" "a1 = filter_a1_map pos tp' a1_map"
      "a2 = filter_a2_map I ts' tp' a2_map"
      unfolding tri_def pair_def by auto
    have tp'_ge: "tp' \<ge> tp - len"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    have tp'_lt_tp: "tp' < tp"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    have ts'_in_lin_tss: "ts' \<in> set (linearize tss)"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    then have ts'_nt: "ts' \<le> nt"
      using valid_shift_aux(1) assms(4) by auto
    then have t_nt: "t \<le> nt"
      unfolding eqs(1) .
    have "table n L (Mapping.keys a1_map)"
      using valid_shift_aux unfolding n_def L_def by auto
    then have a1_tab: "table n L a1"
      unfolding eqs(2) filter_a1_map_def by (auto simp add: table_def)
    note tabR = tabs(2)[unfolded n_def[symmetric] R_def[symmetric]]
    have join_rel2_assms: "L \<subseteq> R" "maskL = join_mask n L"
      using valid_shift_aux unfolding n_def L_def R_def by auto
    have join_rel2_eq: "join rel2 pos a1 = {xs \<in> rel2. proj_tuple_in_join pos maskL xs a1}"
      using join_sub[OF join_rel2_assms(1) a1_tab tabR] join_rel2_assms(2) by auto
    have filter_sub_a2: "\<And>xs m' tp'' tstp. tp'' \<le> tp' \<Longrightarrow>
      Mapping.lookup a2_map' tp'' = Some m' \<Longrightarrow> Mapping.lookup m' xs = Some tstp \<Longrightarrow>
      ts_tp_lt I ts' tp' tstp \<Longrightarrow> (tstp = new_tstp \<Longrightarrow> False) \<Longrightarrow>
      xs \<in> filter_a2_map I ts' tp' a2_map' \<Longrightarrow> xs \<in> a2"
    proof -
      fix xs m' tp'' tstp
      assume m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      have tp''_neq: "tp + 1 \<noteq> tp''"
        using le_less_trans[OF m'_def(1) tp'_lt_tp] by auto
      assume new_tstp_False: "tstp = new_tstp \<Longrightarrow> False"
      show "xs \<in> a2"
      proof (cases "Mapping.lookup a2_map tp''")
        case None
        then have m'_alt: "m' = upd_set' Mapping.empty new_tstp (max_tstp new_tstp)
          {b. (tp'', b) \<in> tmp}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] by (auto split: option.splits if_splits)
        then show ?thesis
          using new_tstp_False m'_def(3)[unfolded m'_alt upd_set'_lookup Mapping.lookup_empty]
          by (auto split: if_splits)
      next
        case (Some m)
        then have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] by (auto split: option.splits if_splits)
        note lookup_m = Some
        show ?thesis
        proof (cases "Mapping.lookup m xs")
          case None
          then show ?thesis
            using new_tstp_False m'_def(3)[unfolded m'_alt upd_set'_lookup]
            by (auto split: if_splits)
        next
          case (Some tstp')
          have tstp_ok: "tstp = tstp' \<Longrightarrow> xs \<in> a2"
            using eqs(3) lookup_m Some m'_def unfolding filter_a2_map_def by auto
          show ?thesis
          proof (cases "xs \<in> {b. (tp'', b) \<in> tmp}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using m'_def(3)[unfolded m'_alt upd_set'_lookup Some] by auto
            show ?thesis
              using lookup_a2_map'[OF lookup_m Some] new_tstp_lt_isl(2)
                tstp_eq new_tstp_False tstp_ok
              by (auto intro: max_tstpE[of new_tstp tstp'])
          next
            case False
            then have "tstp = tstp'"
              using m'_def(3)[unfolded m'_alt upd_set'_lookup Some] by auto
            then show ?thesis
              using tstp_ok by auto
          qed
        qed
      qed
    qed
    have a2_sub_filter: "a2 \<subseteq> filter_a2_map I ts' tp' a2_map'"
    proof (rule subsetI)
      fix xs
      assume xs_in: "xs \<in> a2"
      then obtain tp'' m tstp where m_def: "tp'' \<le> tp'" "Mapping.lookup a2_map tp'' = Some m"
        "Mapping.lookup m xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        using eqs(3)[unfolded filter_a2_map_def] by (auto split: option.splits)
      have tp''_in: "tp'' \<in> {tp - len..tp}"
        using m_def(2) a2_map_keys by (auto intro!: Mapping_keys_intro)
      then obtain m' where m'_def: "Mapping.lookup a2_map' tp'' = Some m'"
        using a2_map'_keys
        by (metis Mapping_keys_dest One_nat_def add_Suc_right add_diff_cancel_right'
            atLeastatMost_subset_iff diff_zero le_eq_less_or_eq le_less_Suc_eq subsetD)
      have tp''_neq: "tp + 1 \<noteq> tp''"
        using m_def(1) tp'_lt_tp by auto
      have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp}"
        using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq] m_def(2)
          upd_nested_lookup] by (auto split: option.splits if_splits)
      show "xs \<in> filter_a2_map I ts' tp' a2_map'"
      proof (cases "xs \<in> {b. (tp'', b) \<in> tmp}")
        case True
        then have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp)"
          unfolding m'_alt upd_set'_lookup m_def(3) by auto
        moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp)"
          using new_tstp_lt_isl(2) lookup_a2_map'[OF m_def(2,3)]
          by (auto intro: max_tstp_intro''[OF _ m_def(4)])
        ultimately show ?thesis
          unfolding filter_a2_map_def using m_def(1) m'_def m_def(4) by auto
      next
        case False
        then have "Mapping.lookup m' xs = Some tstp"
          unfolding m'_alt upd_set'_lookup m_def(3) by auto
        then show ?thesis
          unfolding filter_a2_map_def using m_def(1) m'_def m_def by auto
      qed
    qed
    have "pos \<Longrightarrow> filter_a1_map pos tp' a1_map' = join a1 True rel1"
    proof -
      assume pos: pos
      note tabL = tabs(1)[unfolded n_def[symmetric] L_def[symmetric]]
      have join_eq: "join a1 True rel1 = a1 \<inter> rel1"
        using join_eq[OF tabL a1_tab] by auto
      show "filter_a1_map pos tp' a1_map' = join a1 True rel1"
        using eqs(2) pos tp'_lt_tp unfolding filter_a1_map_def a1_map'_def join_eq
        by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set split: if_splits option.splits
            intro: Mapping_keys_intro dest: Mapping_keys_dest Mapping_keys_filterD)
    qed
    moreover have "\<not>pos \<Longrightarrow> filter_a1_map pos tp' a1_map' = a1 \<union> rel1"
      using eqs(2) tp'_lt_tp unfolding filter_a1_map_def a1_map'_def
      by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set intro: Mapping_keys_intro
          dest: Mapping_keys_filterD Mapping_keys_dest split: option.splits)
    moreover have "memL I (nt - t) \<Longrightarrow> filter_a2_map I ts' tp' a2_map' = a2 \<union> join rel2 pos a1"
    proof (rule set_eqI, rule iffI)
      fix xs
      assume in_int: "memL I (nt - t)"
      assume xs_in: "xs \<in> filter_a2_map I ts' tp' a2_map'"
      then obtain m' tp'' tstp where m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        unfolding filter_a2_map_def by (fastforce split: option.splits)
      show "xs \<in> a2 \<union> join rel2 pos a1"
      proof (cases "tstp = new_tstp")
        case True
        note tstp_new_tstp = True
        have tp''_neq: "tp + 1 \<noteq> tp''"
          using m'_def(1) tp'_lt_tp by auto
        have tp''_in: "tp'' \<in> {tp - len..tp}"
          using m'_def(1,2) tp'_lt_tp a2_map'_keys
          by (auto intro!: Mapping_keys_intro)
        obtain m where m_def: "Mapping.lookup a2_map tp'' = Some m"
          "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] tp''_in a2_map_keys
          by (fastforce dest: Mapping_keys_dest split: option.splits if_splits)
        show ?thesis
        proof (cases "Mapping.lookup m xs = Some new_tstp")
          case True
          then show ?thesis
            using eqs(3) m'_def(1) m_def(1) m'_def tstp_new_tstp
            unfolding filter_a2_map_def by auto
        next
          case False
          then have xs_in_snd_tmp: "xs \<in> {b. (tp'', b) \<in> tmp}"
            using m'_def(3)[unfolded m_def(2) upd_set'_lookup True]
            by (auto split: if_splits)
          then have xs_in_rel2: "xs \<in> rel2"
            unfolding tmp_def
            by (auto split: if_splits option.splits)
          show ?thesis
          proof (cases pos)
            case True
            obtain tp''' where tp'''_def: "Mapping.lookup a1_map (proj_tuple maskL xs) = Some tp'''"
              "if pos then tp'' = max (tp - len) tp''' else tp'' = max (tp - len) (tp''' + 1)"
              using xs_in_snd_tmp m'_def(1) tp'_lt_tp True
              unfolding tmp_def by (auto split: option.splits if_splits)
            have "proj_tuple maskL xs \<in> a1"
              using eqs(2)[unfolded filter_a1_map_def] True m'_def(1) tp'''_def
              by (auto intro: Mapping_keys_intro)
            then show ?thesis
              using True xs_in_rel2 unfolding proj_tuple_in_join_def join_rel2_eq by auto
          next
            case False
            show ?thesis
            proof (cases "Mapping.lookup a1_map (proj_tuple maskL xs)")
              case None
              then show ?thesis
                using xs_in_rel2 False eqs(2)[unfolded filter_a1_map_def]
                unfolding proj_tuple_in_join_def join_rel2_eq
                by (auto dest: Mapping_keys_dest)
            next
              case (Some tp''')
              then have "tp'' = max (tp - len) (tp''' + 1)"
                using xs_in_snd_tmp m'_def(1) tp'_lt_tp False
                unfolding tmp_def by (auto split: option.splits if_splits)
              then have "tp''' < tp'"
                using m'_def(1) by auto
              then have "proj_tuple maskL xs \<notin> a1"
                using eqs(2)[unfolded filter_a1_map_def] True m'_def(1) Some False
                by (auto intro: Mapping_keys_intro)
              then show ?thesis
                using xs_in_rel2 False unfolding proj_tuple_in_join_def join_rel2_eq by auto
            qed
          qed
        qed
      next
        case False
        then show ?thesis
          using filter_sub_a2[OF m'_def _ xs_in] by auto
      qed
    next
      fix xs
      assume in_int: "memL I (nt - t)"
      assume xs_in: "xs \<in> a2 \<union> join rel2 pos a1"
      then have "xs \<in> a2 \<union> (join rel2 pos a1 - a2)"
        by auto
      then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
      proof (rule UnE)
        assume "xs \<in> a2"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
          using a2_sub_filter by auto
      next
        assume "xs \<in> join rel2 pos a1 - a2"
        then have xs_props: "xs \<in> rel2" "xs \<notin> a2" "proj_tuple_in_join pos maskL xs a1"
          unfolding join_rel2_eq by auto
        have ts_tp_lt_new_tstp: "ts_tp_lt I ts' tp' new_tstp"
          using tp'_lt_tp in_int t_nt eqs(1) unfolding new_tstp_def
          by (auto simp add: ts_tp_lt_def elim: contrapos_np)
        show "xs \<in> filter_a2_map I ts' tp' a2_map'"
        proof (cases pos)
          case True
          then obtain tp''' where tp'''_def: "tp''' \<le> tp'"
            "Mapping.lookup a1_map (proj_tuple maskL xs) = Some tp'''"
            using eqs(2)[unfolded filter_a1_map_def] xs_props(3)[unfolded proj_tuple_in_join_def]
            by (auto dest: Mapping_keys_dest)
          define wtp where "wtp \<equiv> max (tp - len) tp'''"
          have wtp_xs_in: "(wtp, xs) \<in> tmp"
            unfolding wtp_def using tp'''_def tmp_def xs_props(1) True by fastforce
          have wtp_le: "wtp \<le> tp'"
            using tp'''_def(1) tp'_ge unfolding wtp_def by auto
          have wtp_in: "wtp \<in> {tp - len..tp}"
            using tp'''_def(1) tp'_lt_tp unfolding wtp_def by auto
          have wtp_neq: "tp + 1 \<noteq> wtp"
            using wtp_in by auto
          obtain m where m_def: "Mapping.lookup a2_map wtp = Some m"
            using wtp_in a2_map_keys Mapping_keys_dest by fastforce
          obtain m' where m'_def: "Mapping.lookup a2_map' wtp = Some m'"
            using wtp_in a2_map'_keys Mapping_keys_dest by fastforce
          have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (wtp, b) \<in> tmp}"
            using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF wtp_neq]
              upd_nested_lookup m_def] by auto
          show ?thesis
          proof (cases "Mapping.lookup m xs")
            case None
            have "Mapping.lookup m' xs = Some new_tstp"
              using wtp_xs_in unfolding m'_alt upd_set'_lookup None by auto
            then show ?thesis
              unfolding filter_a2_map_def using wtp_le m'_def ts_tp_lt_new_tstp by auto
          next
            case (Some tstp')
            have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
              using wtp_xs_in unfolding m'_alt upd_set'_lookup Some by auto
            moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
              using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
              by auto
            ultimately show ?thesis
              using lookup_a2_map'[OF m_def Some] wtp_le m'_def
              unfolding filter_a2_map_def by auto
          qed
        next
          case False
          show ?thesis
          proof (cases "Mapping.lookup a1_map (proj_tuple maskL xs)")
            case None
            then have in_tmp: "(tp - len, xs) \<in> tmp"
              using tmp_def False xs_props(1) by fastforce
            obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
              using a2_map_keys by (fastforce dest: Mapping_keys_dest)
            obtain m' where m'_def: "Mapping.lookup a2_map' (tp - len) = Some m'"
              using a2_map'_keys by (fastforce dest: Mapping_keys_dest)
            have tp_neq: "tp + 1 \<noteq> tp - len"
              by auto
            have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp - len, b) \<in> tmp}"
              using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp_neq]
                upd_nested_lookup m_def] by auto
            show ?thesis
            proof (cases "Mapping.lookup m xs")
              case None
              have "Mapping.lookup m' xs = Some new_tstp"
                unfolding m'_alt upd_set'_lookup None using in_tmp by auto
              then show ?thesis
                unfolding filter_a2_map_def using tp'_ge m'_def ts_tp_lt_new_tstp by auto
            next
              case (Some tstp')
              have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
                unfolding m'_alt upd_set'_lookup Some using in_tmp by auto
              moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
                using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
                by auto
              ultimately show ?thesis
                unfolding filter_a2_map_def using tp'_ge m'_def by auto
            qed
          next
            case (Some tp''')
            then have tp'_gt: "tp' > tp'''"
              using xs_props(3)[unfolded proj_tuple_in_join_def] eqs(2)[unfolded filter_a1_map_def]
                False by (auto intro: Mapping_keys_intro)
            define wtp where "wtp \<equiv> max (tp - len) (tp''' + 1)"
            have wtp_xs_in: "(wtp, xs) \<in> tmp"
              unfolding wtp_def tmp_def using xs_props(1) Some False by fastforce
            have wtp_le: "wtp \<le> tp'"
              using tp'_ge tp'_gt unfolding wtp_def by auto
            have wtp_in: "wtp \<in> {tp - len..tp}"
              using tp'_lt_tp tp'_gt unfolding wtp_def by auto
            have wtp_neq: "tp + 1 \<noteq> wtp"
              using wtp_in by auto
            obtain m where m_def: "Mapping.lookup a2_map wtp = Some m"
              using wtp_in a2_map_keys Mapping_keys_dest by fastforce
            obtain m' where m'_def: "Mapping.lookup a2_map' wtp = Some m'"
              using wtp_in a2_map'_keys Mapping_keys_dest by fastforce
            have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (wtp, b) \<in> tmp}"
              using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF wtp_neq]
                upd_nested_lookup m_def] by auto
            show ?thesis
            proof (cases "Mapping.lookup m xs")
              case None
              have "Mapping.lookup m' xs = Some new_tstp"
                using wtp_xs_in unfolding m'_alt upd_set'_lookup None by auto
              then show ?thesis
                unfolding filter_a2_map_def using wtp_le m'_def ts_tp_lt_new_tstp by auto
            next
              case (Some tstp')
              have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
                using wtp_xs_in unfolding m'_alt upd_set'_lookup Some by auto
              moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
                using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
                by auto
              ultimately show ?thesis
                using lookup_a2_map'[OF m_def Some] wtp_le m'_def
                unfolding filter_a2_map_def by auto
            qed
          qed
        qed
      qed
    qed
    moreover have "\<not> memL I (nt - t) \<Longrightarrow> filter_a2_map I ts' tp' a2_map' = a2"
    proof (rule set_eqI, rule iffI)
      fix xs
      assume out: "\<not> memL I (nt - t)"
      assume xs_in: "xs \<in> filter_a2_map I ts' tp' a2_map'"
      then obtain m' tp'' tstp where m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        unfolding filter_a2_map_def by (fastforce split: option.splits)
      have new_tstp_False: "tstp = new_tstp \<Longrightarrow> False"
        using m'_def t_nt out tp'_lt_tp unfolding eqs(1)
        by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits elim: contrapos_np)
      show "xs \<in> a2"
        using filter_sub_a2[OF m'_def new_tstp_False xs_in] .
    next
      fix xs
      assume "xs \<in> a2"
      then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
        using a2_sub_filter by auto
    qed
    ultimately show "triple_eq_pair (case tri of (t, a1, a2) \<Rightarrow>
      (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2))
      pair (\<lambda>tp'. filter_a1_map pos tp' a1_map') (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map')"
      using eqs unfolding tri_def pair_def by auto
  qed
  have filter_a1_map_rel1: "filter_a1_map pos tp a1_map' = rel1"
    unfolding filter_a1_map_def a1_map'_def using leD lookup_a1_map_keys
    by (force simp add: a1_map_lookup less_imp_le_nat Mapping.lookup_filter
        Mapping_lookup_upd_set keys_is_none_rep dest: Mapping_keys_filterD
        intro: Mapping_keys_intro split: option.splits)
  have filter_a1_map_rel2: "filter_a2_map I nt tp a2_map' =
    (if memL I 0 then rel2 else empty_table)"
  proof (cases "memL I 0")
    case True
    note left_I_zero = True
    have "\<And>tp' m' xs tstp. tp' \<le> tp \<Longrightarrow> Mapping.lookup a2_map' tp' = Some m' \<Longrightarrow>
      Mapping.lookup m' xs = Some tstp \<Longrightarrow> ts_tp_lt I nt tp tstp \<Longrightarrow> xs \<in> rel2"
    proof -
      fix tp' m' xs tstp
      assume lassms: "tp' \<le> tp" "Mapping.lookup a2_map' tp' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I nt tp tstp"
      have tp'_neq: "tp + 1 \<noteq> tp'"
        using lassms(1) by auto
      have tp'_in: "tp' \<in> {tp - len..tp}"
        using lassms(1,2) a2_map'_keys tp'_neq by (auto intro!: Mapping_keys_intro)
      obtain m where m_def: "Mapping.lookup a2_map tp' = Some m"
        "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp}"
        using lassms(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp'_neq]
          upd_nested_lookup] tp'_in a2_map_keys
        by (fastforce dest: Mapping_keys_dest intro: Mapping_keys_intro split: option.splits)
      have "xs \<in> {b. (tp', b) \<in> tmp}"
      proof (rule ccontr)
        assume "xs \<notin> {b. (tp', b) \<in> tmp}"
        then have Some: "Mapping.lookup m xs = Some tstp"
          using lassms(3)[unfolded m_def(2) upd_set'_lookup] by auto
        show "False"
          using lookup_a2_map'[OF m_def(1) Some] lassms(4) left_I_zero
          by (auto simp add: tstp_lt_def ts_tp_lt_def split: sum.splits)
      qed
      then show "xs \<in> rel2"
        unfolding tmp_def by (auto split: option.splits if_splits)
    qed
    moreover have "\<And>xs. xs \<in> rel2 \<Longrightarrow> \<exists>m' tstp. Mapping.lookup a2_map' tp = Some m' \<and>
      Mapping.lookup m' xs = Some tstp \<and> ts_tp_lt I nt tp tstp"
    proof -
      fix xs
      assume lassms: "xs \<in> rel2"
      obtain m' where m'_def: "Mapping.lookup a2_map' tp = Some m'"
        using a2_map'_keys by (fastforce dest: Mapping_keys_dest)
      have tp_neq: "tp + 1 \<noteq> tp"
        by auto
      obtain m where m_def: "Mapping.lookup a2_map tp = Some m"
        "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp}"
        using m'_def a2_map_keys unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq]
          upd_nested_lookup
        by (auto dest: Mapping_keys_dest split: option.splits if_splits)
           (metis Mapping_keys_dest atLeastAtMost_iff diff_le_self le_eq_less_or_eq
            option.simps(3))
      have xs_in_tmp: "xs \<in> {b. (tp, b) \<in> tmp}"
        using lassms left_I_zero unfolding tmp_def by auto
      show "\<exists>m' tstp. Mapping.lookup a2_map' tp = Some m' \<and>
        Mapping.lookup m' xs = Some tstp \<and> ts_tp_lt I nt tp tstp"
      proof (cases "Mapping.lookup m xs")
        case None
        moreover have "Mapping.lookup m' xs = Some new_tstp"
          using xs_in_tmp unfolding m_def(2) upd_set'_lookup None by auto
        moreover have "ts_tp_lt I nt tp new_tstp"
          using left_I_zero new_tstp_def by (auto simp add: ts_tp_lt_def)
        ultimately show ?thesis
          using xs_in_tmp m_def
          unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup by auto
      next
        case (Some tstp')
        moreover have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
          using xs_in_tmp unfolding m_def(2) upd_set'_lookup Some by auto
        moreover have "ts_tp_lt I nt tp (max_tstp new_tstp tstp')"
          using max_tstpE[of new_tstp tstp'] lookup_a2_map'[OF m_def(1) Some] new_tstp_lt_isl left_I_zero
          by (auto simp add: sum.discI(1) new_tstp_def ts_tp_lt_def tstp_lt_def split: sum.splits)
        ultimately show ?thesis
          using xs_in_tmp m_def
          unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup by auto
      qed
    qed
    ultimately show ?thesis
      using True by (fastforce simp add: filter_a2_map_def split: option.splits)
  next
    case False
    note left_I_pos = False
    have "\<And>tp' m xs tstp. tp' \<le> tp \<Longrightarrow> Mapping.lookup a2_map' tp' = Some m \<Longrightarrow>
      Mapping.lookup m xs = Some tstp \<Longrightarrow> \<not>(ts_tp_lt I nt tp tstp)"
    proof -
      fix tp' m' xs tstp
      assume lassms: "tp' \<le> tp" "Mapping.lookup a2_map' tp' = Some m'"
        "Mapping.lookup m' xs = Some tstp"
      from lassms(1) have tp'_neq_Suc_tp: "tp + 1 \<noteq> tp'"
        by auto
      show "\<not>(ts_tp_lt I nt tp tstp)"
      proof (cases "Mapping.lookup a2_map tp'")
        case None
        then have tp'_in_tmp: "tp' \<in> fst ` tmp" and
          m'_alt: "m' = upd_set' Mapping.empty new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp}"
          using lassms(2) unfolding a2_map'_def Mapping.lookup_update_neq[OF tp'_neq_Suc_tp]
            upd_nested_lookup by (auto split: if_splits)
        then have "tstp = new_tstp"
          using lassms(3)[unfolded m'_alt upd_set'_lookup]
          by (auto simp add: Mapping.lookup_empty split: if_splits)
        then show ?thesis
          using False by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits sum.splits)
      next
        case (Some m)
        then have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp}"
          using lassms(2) unfolding a2_map'_def Mapping.lookup_update_neq[OF tp'_neq_Suc_tp]
            upd_nested_lookup by auto
        note lookup_a2_map_tp' = Some
        show ?thesis
        proof (cases "Mapping.lookup m xs")
          case None
          then have "tstp = new_tstp"
            using lassms(3) unfolding m'_alt upd_set'_lookup by (auto split: if_splits)
          then show ?thesis
            using False by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits sum.splits)
        next
          case (Some tstp')
          show ?thesis
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using lassms(3)
              unfolding m'_alt upd_set'_lookup Some by auto
            show ?thesis
              using max_tstpE[of new_tstp tstp'] lookup_a2_map'[OF lookup_a2_map_tp' Some] new_tstp_lt_isl left_I_pos
              by (auto simp add: tstp_eq tstp_lt_def ts_tp_lt_def new_tstp_def split: sum.splits)
          next
            case False
            then show ?thesis
              using lassms(3) lookup_a2_map'[OF lookup_a2_map_tp' Some]
                nat_le_linear[of nt "case tstp of Inl ts \<Rightarrow> ts"]
              unfolding m'_alt upd_set'_lookup Some
              by (auto simp add: ts_tp_lt_def tstp_lt_def split: sum.splits)
          qed
        qed
      qed
    qed
    then show ?thesis
      using False by (auto simp add: filter_a2_map_def empty_table_def split: option.splits)
  qed
  have zip_dist: "zip (linearize tss @ [nt]) ([tp - len..<tp] @ [tp]) =
    zip (linearize tss) [tp - len..<tp] @ [(nt, tp)]"
    using valid_shift_aux(1) by auto
  have list_all2': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map')
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'))
    (drop (length done) (update_until args rel1 rel2 nt auxlist))
    (zip (linearize tss') [tp + 1 - (len + 1)..<tp + 1])"
    unfolding lin_tss' tp_upt_Suc drop_update_until zip_dist
    using filter_a1_map_rel1 filter_a1_map_rel2 list_all2_appendI[OF list_all2_old]
    by auto
  show ?thesis
    using valid_shift_aux len_lin_tss' sorted_lin_tss' set_lin_tss' tab_a1_map'_keys a2_map'_keys'
      len_upd_until sorted_upd_until lookup_a1_map_keys' rev_done' set_take_auxlist'
      lookup_a2_map'_keys list_all2'
    unfolding valid_mmuaux_def add_new_mmuaux_eq valid_mmuaux'.simps
      I_def n_def L_def R_def pos_def by auto
qed

lemma list_all2_check_before: "list_all2 (\<lambda>x y. triple_eq_pair x y f g) xs (zip ys zs) \<Longrightarrow>
  (\<And>y. y \<in> set ys \<Longrightarrow> memR I (nt - y)) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<not>check_before I nt x"
  by (auto simp: in_set_zip elim!: list_all2_in_setE triple_eq_pair.elims)

fun eval_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a table list \<times> 'a mmuaux" where
  "eval_mmuaux args nt aux =
    (let (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    shift_mmuaux args nt aux in
    (rev done, (tp, tss, len, maskL, maskR, a1_map, a2_map, [], 0)))"

lemma valid_eval_mmuaux:
  assumes "valid_mmuaux args cur aux auxlist" "nt \<ge> cur"
    "eval_mmuaux args nt aux = (res, aux')" "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "res = res' \<and> valid_mmuaux args cur aux' auxlist'"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,2) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where shift_aux_def:
    "shift_mmuaux args nt aux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases "shift_mmuaux args nt aux") auto
  have valid_shift_aux: "valid_mmuaux' args cur nt (tp, tss, len, maskL, maskR,
    a1_map, a2_map, done, done_length) auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using valid_shift_mmuaux'[OF assms(1)[unfolded valid_mmuaux_def] assms(2)]
    unfolding shift_aux_def by auto
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have list_all: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux[unfolded valid_mmuaux'.simps]
      list_all2_check_before[OF _ valid_shift_aux(2)] unfolding I_def by fast
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using len_done_auxlist list_all set_drop_auxlist
    by (rule take_takeWhile) assumption+
  have rev_done: "rev done = map proj_thd (take (length done) auxlist)"
    using valid_shift_aux by auto
  then have res'_def: "res' = rev done"
    using eval_until_res[OF assms(4)] unfolding take_auxlist_takeWhile I_def by auto
  then have auxlist'_def: "auxlist' = drop (length done) auxlist"
    using eval_until_auxlist'[OF assms(4)] by auto
  have eval_mmuaux_eq: "eval_mmuaux args nt aux = (rev done, (tp, tss, len, maskL, maskR,
    a1_map, a2_map, [], 0))"
    using shift_aux_def by auto
  show ?thesis
    using assms(3) done_empty_valid_mmuaux'_intro[OF valid_shift_aux(1)]
    unfolding shift_aux_def eval_mmuaux_eq pos_def auxlist'_def res'_def valid_mmuaux_def by auto
qed

definition init_mmuaux :: "args \<Rightarrow> 'a mmuaux" where
  "init_mmuaux args = (0, empty_queue, 0,
  join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
  Mapping.empty, Mapping.update 0 Mapping.empty Mapping.empty, [], 0)"

lemma valid_init_mmuaux: "L \<subseteq> R \<Longrightarrow> valid_mmuaux (init_args I n L R b) 0
  (init_mmuaux (init_args I n L R b)) []"
  unfolding init_mmuaux_def valid_mmuaux_def
  by (auto simp add: init_args_def empty_queue_rep table_def Mapping.lookup_update)

fun length_mmuaux :: "args \<Rightarrow> 'a mmuaux \<Rightarrow> nat" where
  "length_mmuaux args (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    len + done_length"

lemma valid_length_mmuaux:
  assumes "valid_mmuaux args cur aux auxlist"
  shows "length_mmuaux args aux = length auxlist"
  using assms by (cases aux) (auto simp add: valid_mmuaux_def dest: list_all2_lengthD)

(* begin trigger (mtaux) *)

(* simply stores all tables for \<phi> and \<psi> in [0, b] *)
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"

definition time :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> ts" where
  "time = fst"

definition relL :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relL = (fst o snd)"

definition relR :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relR = (snd o snd)"

type_synonym 'a mmtaux = "
  ts \<times>                                 \<comment> \<open>the newest timestamp\<close>
  nat \<times> nat \<times> nat \<times>                   \<comment> \<open>index of the first queue entry in data_prev, data_in and the last index of data_in\<close>
  bool list \<times>                          \<comment> \<open>maskL, i.e. all free variables of R \\ L are masked\<close>
  bool list \<times>                          \<comment> \<open>maskR, i.e. all free variables of L \\ R are masked\<close>
  (ts \<times> 'a table \<times> 'a table) queue \<times>  \<comment> \<open>data_prev: all databases containing the tuples satisfying the lhs or the rhs where the timestamp doesn't yet satisfy memL\<close>
  (ts \<times> 'a table) queue \<times>              \<comment> \<open>data_in: all databases containing the tuples satisfying the rhs where the ts is in the interval\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_in for once\<close>
  'a table \<times>                            \<comment> \<open>Mapping.keys tuple_in_once, just here for performance improvements\<close>
  (('a tuple, nat) mapping) \<times>          \<comment> \<open>tuple_since for historically. stores the index since when the rhs of the formula holds\<close>
  ('a table) \<times>
  ('a table)                            \<comment> \<open>the set of tuples currently satisfying \<psi> S_[0, \<infinity>] (\<psi> \<and> \<phi>)\<close>
"

fun mmtaux_data_prev :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue" where
  "mmtaux_data_prev (_, _, _, _, _, _, data_prev, _) = data_prev"

fun mmtaux_data_in :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table) queue" where
  "mmtaux_data_in (_, _, _, _, _, _, _, data_in, _) = data_in"

definition ts_tuple_rel_binary :: "(ts \<times> 'a table \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple \<times> 'a tuple) set" where
  "ts_tuple_rel_binary ys = {(t, as, bs). \<exists>X Y. as \<in> X \<and> bs \<in> Y \<and> (t, X, Y) \<in> ys}"

abbreviation "ts_tuple_rel_binary_lhs \<equiv> ts_tuple_rel_f fst"
abbreviation "ts_tuple_rel_binary_rhs \<equiv> ts_tuple_rel_f snd"

definition auxlist_data_prev :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_prev args mt auxlist = filter (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) auxlist"

definition auxlist_data_in :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_in args mt auxlist = filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist"

definition tuple_since_tp where
  "tuple_since_tp args as lin_data_in idx_oldest idx_mid idx = (
    (lin_data_in \<noteq> []) \<and>
    idx < idx_mid \<and>
    (\<forall>(t, r) \<in> set (drop (idx-idx_oldest) lin_data_in). 
      as \<in> r
    ) \<and>
    (idx > idx_oldest \<longrightarrow> as \<notin> (snd (lin_data_in!(idx-idx_oldest-1))))
  )"

definition tuple_since_lhs where
  "tuple_since_lhs tuple lin_data_in args maskL auxlist_in = ((lin_data_in \<noteq> []) \<and> ( \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
    \<exists>n \<in> {0..<length lin_data_in}. \<comment> \<open>dropping less then length guarantees length suffix > 0\<close>
      let suffix = drop n auxlist_in in (
        (\<forall>(t, l, r) \<in> set suffix.
          tuple \<in> r
        ) \<and>
        (
          join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)
        )
    )
  ))"

fun valid_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mtaux \<Rightarrow> bool" where
  "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist \<longleftrightarrow>
    (if mem (args_ivl args) 0 then (args_L args) \<subseteq> (args_R args) else (args_L args) = (args_R args)) \<and>
    (\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args) \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    (\<forall>(t, relL, relR) \<in> set auxlist. table (args_n args) (args_L args) relL \<and> table (args_n args) (args_R args) relR) \<and>
    table (args_n args) (args_L args) (Mapping.keys tuple_in_once) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_since_hist) \<and>
    (\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as) \<and>
    (\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as) \<and>
    (\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in))). wf_tuple (args_n args) (args_R args) as) \<and>
    cur = mt \<and>
    \<comment> \<open>all valid rhs/\<psi> tuples in data_in should have a valid entry in tuple_since_hist, as it is shifted\<close>
    ts_tuple_rel_binary_rhs (set (auxlist_data_in args mt auxlist)) =
    ts_tuple_rel (set (linearize data_in)) \<and>
    \<comment> \<open>the entries stored should be the same, hence they're sorted as well\<close>
    sorted (map fst auxlist) \<and>
    auxlist_data_prev args mt auxlist = (linearize data_prev) \<and>
    auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist \<and>
    length (linearize data_prev) + idx_mid = idx_next  \<and>  \<comment> \<open>length (linearize data_prev) = idx_next - idx_mid\<close>
    map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in) \<and>
    auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist \<and>
    length (linearize data_in) + idx_oldest = idx_mid \<and> \<comment> \<open>length (linearize data_in) = idx_mid - idx_oldest\<close>
    \<comment> \<open>also all tuples in auxlist (and hence data_prev/data_in) satisfy memR \<close>
    (\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db)) \<and>
     \<comment> \<open>check whether tuple_in once contains the newest occurence of the tuple satisfying the lhs\<close>
    newest_tuple_in_mapping fst data_prev tuple_in_once (\<lambda>x. True) \<and>
    (\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l (proj_tuple maskL as)) \<and>
    (\<forall>as. (case Mapping.lookup tuple_since_hist as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx)
    ) \<and>
    \<comment> \<open>conditions for sat / trigger conditions\<close>
    (\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
      (\<not>is_empty data_in) \<and> ( \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
        \<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r
    )) \<and>
    (\<forall>tuple. tuple \<in> since_sat \<longrightarrow>
      ((tuple \<in> hist_sat) \<or> tuple_since_lhs tuple (linearize data_in) args maskL (auxlist_data_in args mt auxlist))
    ) \<and>
    (\<forall>tuple. tuple_since_lhs tuple (linearize data_in) args maskL (auxlist_data_in args mt auxlist) \<longrightarrow>
      tuple \<in> since_sat
    ) \<and>
    tuple_in_once_keys = Mapping.keys tuple_in_once
  "

definition init_mmtaux :: "args \<Rightarrow> 'a mmtaux" where
  "init_mmtaux args = (0, 0, 0, 0, join_mask (args_n args) (args_L args),
  join_mask (args_n args) (args_R args), empty_queue, empty_queue, Mapping.empty, {}, Mapping.empty, {}, {})"

lemma valid_init_mmtaux: "(
    if (mem I 0)
      then
        L \<subseteq> R
      else 
        L = R
    ) \<Longrightarrow>
    \<not>mem I 0 \<longrightarrow> pos \<Longrightarrow>
    let args = init_args I n L R pos in
    valid_mmtaux args 0 (init_mmtaux args) []"
  unfolding init_mmtaux_def
  by (auto simp add: init_args_def empty_queue_rep
      Mapping.lookup_empty safe_max_def table_def newest_tuple_in_mapping_def
      ts_tuple_rel_binary_def ts_tuple_rel_f_def
      auxlist_data_prev_def auxlist_data_in_def is_empty_alt tuple_since_tp_def tuple_since_lhs_def)

fun result_mmtaux :: "args \<Rightarrow> event_data mmtaux \<Rightarrow> (nat set \<times> event_data table)" where
  "result_mmtaux args (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) = 
  (
    \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
    if (is_empty data_in) then
      ({}, {replicate (args_n args) None})
    else
      (args_R args, tuple_in_once_keys \<union> hist_sat \<union> since_sat)
  )
"

lemma sorted_filter_dropWhile_memL:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). memL (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs"
      by auto
    moreover have "dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs)"
      by auto
    have dropWhile_IH: "dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#xs"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = x#xs"
        using filter_IH
        by auto
      then show ?thesis using dropWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) x)" by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma sorted_filter_dropWhile_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs"
      by auto
    moreover have "dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs)"
      by auto
    have dropWhile_IH: "dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#xs"
      using mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = x#xs"
        using filter_IH
        by auto
      then show ?thesis using dropWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x)" using memR_antimono by auto
      then show ?thesis using mem by auto
    qed
  qed
qed

lemma sorted_filter_takeWhile_memL:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). memL (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).memL (args_ivl args) (mt - t)) xs)"
      by auto
    moreover have "takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#(takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = (filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs)"
      by auto
    have takeWhile_IH: "takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = []"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = []"
        using filter_IH
        by (simp add: case_prod_beta')
      then show ?thesis using takeWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) x)" by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma sorted_filter_takeWhile_not_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).\<not>memR (args_ivl args) (mt - t)) xs)"
      by auto
    moreover have "takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#(takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = (filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs)"
      by auto
    have takeWhile_IH: "takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = []"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = []"
        using filter_IH
        by (simp add: case_prod_beta')
      then show ?thesis using takeWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x)"
        using memR_antimono by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma data_in_mem:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set (linearize data_in)"
  shows "mem (args_ivl args) (mt - (fst db))"
proof (cases db)
  case (Pair t r)
  from assms(1) have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    by auto
  then have "(t, r) \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
    using Pair assms(2)
    by auto
  then obtain l where "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
    by auto
  then show ?thesis
    unfolding auxlist_data_in_def
    using set_filter[of "\<lambda>(t, _, _). mem (args_ivl args) (mt - t)" auxlist] Pair
    by auto
qed

lemma data_prev_mem:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set (linearize data_prev)"
  shows "\<not>memL (args_ivl args) (mt - (time db))"
proof -
  from assms(1) have "auxlist_data_prev args mt auxlist = linearize data_prev"
    by simp
  then have "db \<in> set (auxlist_data_prev args mt auxlist)" using assms(2) by auto
  then show ?thesis
    unfolding auxlist_data_prev_def time_def
    using set_filter[of "\<lambda>(t, _, _). \<not>memL (args_ivl args) (mt - t)" auxlist]
    by auto
qed


lemma data_sorted:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "sorted (map fst (linearize data_prev))" "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` (set (linearize data_in)). \<forall>t' \<in> fst ` (set (linearize data_prev)). t < t'"
proof -
  from assms have sorted: "sorted (map fst auxlist)"
    by auto
  from assms have data_props: 
    "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    by auto
  
  show "sorted (map fst (linearize data_prev))"
    using data_props(1) sorted sorted_filter
    unfolding auxlist_data_prev_def
    by metis

  have "\<forall>tuple. fst ((\<lambda> (t, l, r). (t, r)) tuple) = fst tuple"
    by auto
  then have "map fst (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)) = map fst (auxlist_data_in args mt auxlist)"
    by auto

  moreover from sorted have "sorted (map fst (auxlist_data_in args mt auxlist))"
    unfolding auxlist_data_in_def
    using sorted_filter
    by auto

  ultimately have "sorted (map fst (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)))"
    by (simp only: )

  then show "sorted (map fst (linearize data_in))"
    using data_props(2)
    by simp

  {
    fix t t'
    assume "t \<in> fst ` (set (linearize data_in))" "t' \<in> fst ` (set (linearize data_prev))"
    then have memL: "\<not>memL (args_ivl args) (mt - t')" "memL (args_ivl args) (mt - t)"
      using data_in_mem[OF assms(1)] data_prev_mem[OF assms(1)]
      unfolding time_def
      by auto
    {
      assume "t \<ge> t'"
      then have "False" using memL memL_mono by auto
    }
    then have "t < t'" using not_le_imp_less by blast
  }
  then show "\<forall>t \<in> fst ` (set (linearize data_in)). \<forall>t' \<in> fst ` (set (linearize data_prev)). t < t'" by auto
qed

lemma tuple_in_once_mem0:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "mem (args_ivl args) 0"
  shows "tuple_in_once = Mapping.empty"
proof -
  from assms(2) have memL_all: "\<forall>t. memL (args_ivl args) t" by auto
  from assms(1) have "auxlist_data_prev args mt auxlist = linearize data_prev"
    by simp
  then have "linearize data_prev = []"
    using memL_all
    unfolding auxlist_data_prev_def
    by auto
  moreover from assms(1) have "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l (proj_tuple maskL as))"
    by simp
  ultimately have "Mapping.keys tuple_in_once = {}"
    using Mapping_keys_dest
    by fastforce
  then show ?thesis
    by (simp add: Mapping.lookup_empty keys_dom_lookup mapping_eqI)
qed

lemma auxlist_mem_or:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> (set auxlist)"
  shows "(((\<lambda> (t, l, r). (t, r)) db) \<in> set (linearize data_in) \<and> db \<notin> set (linearize data_prev)) \<and> memL (args_ivl args) (mt - time db) \<or> (((\<lambda> (t, l, r). (t, r)) db) \<notin> set (linearize data_in) \<and> db \<in> set (linearize data_prev)) \<and> \<not>memL (args_ivl args) (mt - time db)"
proof (cases "memL (args_ivl args) (mt - (time db))")
  define db' where "db' = ((\<lambda> (t, l, r). (t, r)) db)"
  case True
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    by auto
  from assms have mem: "memR (args_ivl args) (mt - time db)" by auto

  {
    assume "db \<in> set (linearize data_prev)"
    then have "db \<in> set (auxlist_data_prev args mt auxlist)"
      using data_props(1)
      by auto
    then have "\<not>memL (args_ivl args) (mt - (time db))"
      unfolding auxlist_data_prev_def time_def
      by auto
    then have "False"
      using True
      by auto
  }
  then have not_prev: "db \<notin> set (linearize data_prev)" by auto

  have db_mem: "db \<in> set (auxlist_data_in args mt auxlist)"
    using True assms(2) mem
    unfolding auxlist_data_in_def time_def
    by auto
  then have "(\<lambda> (t, l, r). (t, r)) db \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
    by auto
  then have "db' \<in> set (linearize data_in)"
    using data_props(2) db'_def
    by auto
  moreover have "memL (args_ivl args) (mt - time db)"
    using db_mem
    unfolding auxlist_data_in_def time_def
    by auto
  ultimately show ?thesis using db'_def not_prev by blast
next
  define db' where "db' = ((\<lambda> (t, l, r). (t, r)) db)"
  case False
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    by auto
  from assms have mem: "memR (args_ivl args) (mt - time db)" by auto
  have time_eq: "fst db = fst db'" using db'_def by (simp add: case_prod_beta)

  {
    assume "db' \<in> set (linearize data_in)"
    then have "db' \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
      using data_props(2)
      by auto
    then have "\<exists>l. (fst db', l, snd db') \<in> set (auxlist_data_in args mt auxlist)"
      by auto
    then have "mem (args_ivl args) (mt - (time db))"
      using time_eq
      unfolding auxlist_data_in_def time_def
      by auto
    then have "False"
      using False
      by auto
  }
  then have not_in: "db' \<notin> set (linearize data_in)" by auto
  
  have "db \<in> set (auxlist_data_prev args mt auxlist)"
    using False assms(2)
    unfolding auxlist_data_prev_def time_def
    by auto
  then have "db \<in> set (linearize data_prev)"
    using data_props(1) db'_def
    by auto
  then show ?thesis using not_in db'_def False by blast
qed

lemma auxlist_mem_data_in:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set auxlist"
  assumes "mem (args_ivl args) (mt - (time db))"
  shows "(\<lambda> (t, l, r). (t, r)) db \<in> set (linearize data_in)"
  using auxlist_mem_or[OF assms(1) assms(2)] assms(3)
  by auto


lemma data_prev_ts_props:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> mt \<and> \<not> memL (args_ivl args) (cur - t)"
proof -
  from assms have data_props:
    "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    by auto
  from assms have "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db))"
    by auto
  moreover from assms have time: "cur = mt" by auto
  ultimately have memR: "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (cur - time db))"
    by auto

  {
    fix t
    assume "t \<in> fst ` set (linearize data_prev)"
    then obtain db where db_props: "t = fst db" "db \<in> set (linearize data_prev)"
      by auto
    then have "db \<in> set (auxlist_data_prev args mt auxlist)" using data_props by auto
    then have "\<not>memL (args_ivl args) (cur - t)" "db \<in> set auxlist"
      unfolding auxlist_data_prev_def db_props(1)
      using time
      by auto
    moreover have "t \<le> mt"
      using calculation(2) memR
      unfolding time_def db_props(1)
      by auto
    ultimately have "t \<le> mt" "\<not>memL (args_ivl args) (cur - t)" by auto
  }
  then show ?thesis by auto
qed

lemma data_in_ts_props:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "\<forall>t \<in> fst ` set (linearize data_in). t \<le> mt \<and> memL (args_ivl args) (cur - t)"
proof -
  from assms have data_props:
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
    by auto
  from assms have "(\<forall>db \<in> set auxlist. time db \<le> mt \<and>  memR (args_ivl args) (mt - time db))"
    by auto
  moreover from assms have time: "cur = mt" by auto
  ultimately have memR: "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (cur - time db))"
    by auto

  {
    fix t
    assume "t \<in> fst ` set (linearize data_in)"
    then obtain db where db_props: "t = fst db" "db \<in> set (linearize data_in)"
      by auto
    then obtain db' where db'_props: "db = (\<lambda> (t, l, r). (t, r)) db'" "db' \<in> set (auxlist_data_in args mt auxlist)"
      using data_props(1)
      by (metis (no_types, lifting) image_iff image_set)
    then have same_time: "fst db' = t"
      unfolding db_props(1)
      by (simp add: case_prod_beta)

    then have "mem (args_ivl args) (cur - t)" "db' \<in> set auxlist"
      using db'_props(2) time
      unfolding auxlist_data_in_def
      by auto
    moreover have "t \<le> mt"
      using calculation(2) memR same_time
      unfolding time_def db_props(1)
      by auto
    ultimately have "t \<le> mt" "memL (args_ivl args) (cur - t)" by auto
  }
  then show ?thesis by auto
qed

lemma auxlist_index_time_mono:
  assumes "valid_mmtaux args cur (nt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "i \<le> j" "j \<in> {0..<(length auxlist)}"
  shows "fst (auxlist!i) \<le> fst (auxlist!j)"
proof -
  from assms have "sorted (map fst auxlist)" by auto
  then have sorted: "\<forall>i. \<forall>j \<in> {0..<(length auxlist)}.
    i \<le> j \<longrightarrow> fst (auxlist!i) \<le> fst (auxlist!j)"
    by (simp add: sorted_iff_nth_mono)
  then show "fst (auxlist!i) \<le> fst (auxlist!j)"
    using sorted assms(2-3)
    by auto
qed

lemma auxlist_time_index_strict_mono:
  assumes "valid_mmtaux args cur (nt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "i \<in> {0..<(length auxlist)}"
  assumes "fst (auxlist!i) < fst (auxlist!j)" (* t < t' *)
  shows "i < j"
proof -
    {
      assume assm: "j \<le> i"
      then have "False"
        using auxlist_index_time_mono[OF assms(1) assm assms(2)] assms(3)
        by auto
    }
    then show "i < j" using not_le_imp_less by blast
  qed

lemma data_in_auxlist_nonempty:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0) = (\<not> is_empty (data_in))"
proof (rule iffI)
  assume assm: "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
  {
    assume empty: "set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) = {}"
    {
      assume "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
      then have "\<exists>x. x \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
        using nth_mem by blast
      then have "False" using empty by auto
    }
    then have "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) = 0"
      by auto
    then have "False" using assm by auto
  }
  then obtain db where db_props: "db \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
    by auto
  then have "db \<in> set auxlist" "mem (args_ivl args) (mt - fst db)" by auto
  then have "(\<lambda> (t, l, r). (t, r)) db \<in> set (linearize data_in)"
    using auxlist_mem_data_in[OF assms(1), of db]
    unfolding time_def
    by blast
  then have "set (linearize data_in) \<noteq> {}" by auto
  then show "\<not> is_empty (data_in)"
    using is_empty_alt
    by auto
next
    from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
      by auto

    assume "\<not> is_empty (data_in)"
    then have "set (linearize data_in) \<noteq> {}" using is_empty_alt by auto
    then obtain db where db_props: "db \<in> set (linearize data_in)"
      by (meson equals0I)
    then have db_mem: "db \<in> set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist))"
      using data_props(2)
      unfolding auxlist_data_in_def
      by auto
    then obtain l where "(fst db, l, snd db) \<in> set (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
      by auto
    then show auxlist_nonempty: "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0)"
      using length_pos_if_in_set[of "(fst db, l, snd db)" "filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist"]
      by auto
  qed

lemma valid_mmtaux_nonempty:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0) = (\<not> is_empty data_in)"
proof -
  from assms(1) have data_in_equiv:
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
      by auto
    show ?thesis
    proof (rule iffI)
      assume "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
      then have "length (auxlist_data_in args mt auxlist) > 0"
        using auxlist_data_in_def[of args mt auxlist]
        by auto
      then have "{} \<noteq> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"        
        by auto
      then have "(linearize data_in) \<noteq> []"
        using data_in_equiv
        by auto
      then show "\<not> is_empty data_in"
        using is_empty_alt
        by auto
    next
      assume "\<not> is_empty data_in"
      then have "\<exists>e. e \<in> set (linearize data_in)"
        using is_empty_alt nth_mem
        by blast
      then have "{} \<noteq> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
        using data_in_equiv
        by auto
      then have "{} \<noteq> set (auxlist_data_in args mt auxlist)"
        by auto
      then have "length (auxlist_data_in args mt auxlist) > 0"
        by auto 
      then show "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
        unfolding auxlist_data_in_def 
        by auto
    qed
  qed

lemma valid_result_mmtaux_unfolded: 
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "result_mmtaux args (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) = trigger_results args cur auxlist"
proof -
  define aux where "aux = (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"
  define I where "I = args_ivl args"
  from assms(1) have time: "mt = cur" by auto
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    by auto
  from assms(1) have sorted: "sorted (map fst auxlist)"
    by auto
  {
    assume non_empty_assm: "\<not>is_empty data_in"
    note non_empty_alt = non_empty_assm data_in_auxlist_nonempty[OF assms(1)] time
  
    {
      fix tuple
      assume assm: "tuple \<in> snd (result_mmtaux args aux)"
      then have non_empty: "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
        using non_empty_assm valid_mmtaux_nonempty[OF assms(1)]
        by auto
  
      {
        assume "tuple \<in> hist_sat"
        then have hist:
          "\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r"
          "(\<not>is_empty data_in)"
          "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
          "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in))). wf_tuple (args_n args) (args_R args) as)"
          using assms(1)
          by auto
        then obtain t l r where "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
          using is_empty_alt[of data_in]
          by (metis length_greater_0_conv length_map nth_mem proj_thd.cases)
        then have "tuple \<in> r" "(t, r) \<in> set (linearize data_in)"
          using hist(1) set_map[of "(\<lambda> (t, l, r). (t, r))" "(auxlist_data_in args mt auxlist)", unfolded hist(3)]
          by (auto simp add: rev_image_eqI)
        then have wf: "wf_tuple (args_n args) (args_R args) tuple"
          using hist(4)
          by auto
        {
          fix i
          assume i_props: "i \<in> {0..<(length auxlist)}" "mem (args_ivl args) (mt - fst (auxlist!i))"
          then have "auxlist!i \<in> set (auxlist_data_in args mt auxlist)"
            by (simp add: auxlist_data_in_def case_prod_unfold)
          then have "tuple \<in> (snd o snd) (auxlist!i)" using hist by auto
        }
        then have "(\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (mt - t) \<longrightarrow> tuple \<in> r
        )" by (simp add: case_prod_beta')
        then have "tuple \<in> snd (trigger_results args mt auxlist)"
          using non_empty wf
          by auto
      }
      then have hist_sat_mem: "tuple \<in> hist_sat \<Longrightarrow> tuple \<in> snd (trigger_results args mt auxlist)"
        by auto

      have "tuple_in_once_keys = Mapping.keys tuple_in_once"
        using assms(1)
        by auto
      then have "tuple \<in> (Mapping.keys tuple_in_once) \<or> tuple \<in> hist_sat \<or> tuple \<in> since_sat"
        using assm non_empty_assm
        by (simp add: aux_def split: if_splits)
      moreover {
        assume assm: "tuple \<in> (Mapping.keys tuple_in_once)"
        then have "newest_tuple_in_mapping fst data_prev tuple_in_once (\<lambda>x. True)"
          using assms(1)
          by auto
        then have "Mapping.lookup tuple_in_once tuple =
          safe_max (
            fst ` {
             tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
             tuple = snd tas
            }
          )"
          unfolding newest_tuple_in_mapping_def
          by auto
        moreover have "\<exists>t. Mapping.lookup tuple_in_once tuple = Some t"
          using assm
          by (simp add: Mapping_keys_dest)
        then obtain t where t_props: "Mapping.lookup tuple_in_once tuple = Some t"
          by auto
        from assms(1) have "\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l (proj_tuple maskL as)"
          by auto
        then have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l (proj_tuple maskL tuple)"
          using assm t_props
          by fastforce
        then obtain db l r where db_props: "db = (t, l, r)" "db \<in> set (linearize data_prev)" "join_cond (args_pos args) l (proj_tuple maskL tuple)"
          unfolding ts_tuple_rel_f_def
          by auto
        then obtain j where j_props: "db = auxlist!j" "j \<in> {0..<(length auxlist)}"
          using data_props(1)
          unfolding auxlist_data_prev_def
          by (metis (no_types, lifting) atLeastLessThan_iff filter_is_subset in_set_conv_nth leI not_less_zero subsetD)
        
        {
          fix i
          define dbi where "dbi = auxlist!i"
          assume i_props: "i \<in> {0..<(length auxlist)}" "mem (args_ivl args) (mt - time dbi)"
          {
            assume "j \<le> i"
            then have "fst (auxlist ! j) \<le> fst (auxlist ! i)"
              using sorted i_props(1)
              by (simp add: sorted_iff_nth_mono)
            then have j_memL: "memL (args_ivl args) (mt - time (auxlist!j))"
              using i_props(2) memL_mono[of "args_ivl args" "mt - time dbi" "mt - time (auxlist!j)"]
              unfolding time_def dbi_def
              by auto
            then have "auxlist!j \<in> set (linearize data_prev)"
              using j_props db_props
              by auto
            then have "\<not>memL (args_ivl args) (mt - time (auxlist!j))"
              using data_prev_mem[OF assms(1)]
              by auto
            then have "False" using j_memL by blast
          }
          then have j_ge_i: "i < j" using not_le_imp_less by blast
          then have "j \<in> {i<..<(length auxlist)}" using j_props(2)
            by simp
          moreover have "join_cond (args_pos args) ((fst o snd) (auxlist!j)) (proj_tuple maskL tuple)"
            using db_props j_props(1)
            by auto
          ultimately have "(\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
            )"
          using relL_def
          by metis
        }
        moreover have "maskL = join_mask (args_n args) (args_L args)"
          using assms(1)
          by auto
        ultimately have "(\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (mt - t) \<longrightarrow>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
            )
        )"
          by (fastforce simp add: case_prod_beta' time_def)
        moreover have "wf_tuple (args_n args) (args_R args) tuple"
        proof -
          have "auxlist_data_prev args mt auxlist = (linearize data_prev)"
            using assms(1)
            by auto
          then have "auxlist_data_prev args mt auxlist \<noteq> []"
            using db_props
            by auto
          then have "\<not>mem (args_ivl args) 0"
            using memL_mono[of "args_ivl args" 0]
            unfolding auxlist_data_prev_def
            by auto
          then have "(args_L args) = (args_R args)"
            using assms(1)
            by auto
          then have "table (args_n args) (args_R args) (Mapping.keys tuple_in_once)"
            using assms(1)
            by auto
          then show ?thesis
            using assm
            unfolding table_def
            by blast
        qed                
        ultimately have "tuple \<in> snd (trigger_results args mt auxlist)"
          using non_empty
          unfolding relL_def
          by fastforce
      }
      moreover {
        assume "tuple \<in> since_sat"
        moreover have "(\<forall>tuple. tuple \<in> since_sat \<longrightarrow>
          ((tuple \<in> hist_sat) \<or> tuple_since_lhs tuple (linearize data_in) args maskL (auxlist_data_in args mt auxlist))
        )"
          using assms(1)
          unfolding valid_mmtaux.simps
          apply -
          apply (erule conjE)+
          apply assumption
          done
        moreover have "length (linearize data_in) = length (auxlist_data_in args mt auxlist)"
        proof -
          have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
            using assms(1)
            by auto
          then show ?thesis
            by (metis length_map)
        qed
        ultimately have "(tuple \<in> hist_sat) \<or> (\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (
              join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)
            )
          ))"
          unfolding tuple_since_lhs_def
          by fastforce
        moreover {
          assume "tuple \<in> hist_sat"
          then have "tuple \<in> snd (trigger_results args mt auxlist)"
            using hist_sat_mem by auto
        }
        moreover {
          assume "\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (
              join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)
            )
          )"
  
          then obtain n where n_def:
            "n \<in> {0..<length (auxlist_data_in args mt auxlist)}"
            "let suffix = drop n (auxlist_data_in args mt auxlist) in (
                (\<forall>(t, l, r) \<in> set suffix.
                  tuple \<in> r
                ) \<and>
                (
                  join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)
                )
            )"
            by blast
          define suffix where "suffix = drop n (auxlist_data_in args mt auxlist)"
          then have suffix_rhs: "\<forall>(t, l, r) \<in> set suffix. tuple \<in> r"
            using n_def(2)
            by meson
          
  
          have suffix_length: "length suffix > 0" "length suffix = length (auxlist_data_in args mt auxlist) - n"
            using suffix_def n_def(1)
            by auto
          then obtain t l r where tlr:
            "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
            "tuple \<in> r"
            using suffix_rhs
            unfolding suffix_def
            by (metis case_prodE hd_in_set in_set_dropD length_greater_0_conv)
          moreover have in_props:
            "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in))). wf_tuple (args_n args) (args_R args) as)"
            "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
            using assms(1)
            by auto
          ultimately have "(t, r) \<in> set (linearize data_in)"
            by (metis (no_types, lifting) case_prod_conv list.set_map pair_imageI)
          then have wf: "wf_tuple (args_n args) (args_R args) tuple"
            using tlr in_props(1)
            by auto
  
          have idx_shift: "\<forall>i\<in>{0..<length suffix}. suffix!i = (auxlist_data_in args mt auxlist)!(i+n)"
            using suffix_def n_def(1)
            by (simp add: add.commute)
          have suffix_lhs: "join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)"
            using suffix_def n_def(2)
            by meson
          
          moreover have data_in_equiv: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
            using assms(1)
            by auto
          moreover have "(auxlist_data_in args mt auxlist)!n = auxlist!n"
            using n_def(1)
            by (simp add: calculation(2))
          ultimately have since: "join_cond (args_pos args) (relL (auxlist!n)) (proj_tuple maskL tuple)"
            using idx_shift suffix_length
            unfolding suffix_def
            by (auto simp add: hd_drop_conv_nth)
          
          have n_le_auxlist: "n < (length auxlist)"
            using n_def(1)
            unfolding auxlist_data_in_def
            by (meson atLeastLessThan_iff diff_le_self length_filter_le less_le_trans)
          {
            fix i
            assume i_props: "i \<in> {0..<n}"
            then have "n \<in> {i<..<(length auxlist)}"
              using n_le_auxlist
              by auto
            moreover have
              "join_cond (args_pos args) (relL (auxlist!n)) (proj_tuple maskL tuple)"
              using since
              by auto
            ultimately have "(\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
              )"
              using relL_def by blast
          }
          then have "(\<forall>i \<in> {0..<n}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> 
              (\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
              )
          )"
            by (simp add: case_prod_beta')
          then have trigger_res_1: "(\<forall>i \<in> {0..<n}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
              )
            )
          )" by fastforce
          {
            fix i
            assume i_props: "i \<in> {n..<(length auxlist)}" "mem (args_ivl args) (mt - time (auxlist!i))"
            {
              assume "i \<ge> n + length suffix"
              then have i_ge: "i \<ge> length (auxlist_data_in args mt auxlist)"
                using suffix_length n_def(1)
                by auto
              then have idx_shift: "auxlist!i = (drop (length (auxlist_data_in args mt auxlist)) auxlist)!(i - length (auxlist_data_in args mt auxlist))"
                by (simp add: data_in_equiv)
              have
                "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
                "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
                using assms(1)
                by auto
              then have data_prev_equiv: "auxlist_data_prev args mt auxlist = drop (length (auxlist_data_in args mt auxlist)) auxlist"
                by (metis length_map)
              then have "auxlist!i = (auxlist_data_prev args mt auxlist)!(i - length (auxlist_data_in args mt auxlist))"
                using idx_shift
                by auto
              then have "auxlist!i \<in> set (auxlist_data_prev args mt auxlist)"
                using i_ge i_props(1) data_prev_equiv
                by (metis (no_types, lifting) add.commute atLeastLessThan_iff in_set_conv_nth le_add_diff_inverse length_drop less_diff_conv)
              moreover have "auxlist_data_prev args mt auxlist = (linearize data_prev)"
                using assms(1)
                by auto
              ultimately have "auxlist!i \<in> set (linearize data_prev)" by auto
              then have "\<not> memL (args_ivl args) (mt - time (auxlist!i))"
                using data_prev_mem[OF assms(1), of "auxlist!i"]
                by auto
              then have "False" using i_props(2) by auto
            }
            then have "i < n + length suffix" using not_le_imp_less by blast
            then have "i < length (auxlist_data_in args mt auxlist)"
              using suffix_length
              by auto
            then have i_props': "i \<in> {n..<length (auxlist_data_in args mt auxlist)}"
              using i_props
              by auto
            then have "suffix!(i-n) = (auxlist_data_in args mt auxlist)!i"
              unfolding suffix_def
              by simp
            moreover have "(auxlist_data_in args mt auxlist)!i = auxlist!i"
              using data_in_equiv i_props'
              by simp
            ultimately have "suffix!(i-n) = auxlist!i" by auto
            then have "auxlist!i \<in> set suffix"
              using i_props'
              by (smt atLeastLessThan_iff dual_order.trans less_diff_iff less_or_eq_imp_le nth_mem suffix_length(2))
            (* "\<forall>i\<in>{0..<length suffix}. suffix!i = (auxlist_data_in args mt auxlist)!(i+n)" *)
            then have "tuple \<in> (snd o snd) (auxlist!i)"
              using suffix_rhs
              by auto
          }
          then have "(\<forall>i \<in> {n..<(length auxlist)}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> tuple \<in> r
          )"
            unfolding time_def
            by (simp add: case_prod_beta')
          then have "(\<forall>i \<in> {n..<(length auxlist)}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
              )
            )
          )"
            by auto
          then have "(\<forall>i \<in> {0..<(length auxlist)}.
            let (t, l, r) = auxlist!i in
            mem (args_ivl args) (mt - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist)}.
                join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
              )
            )
          )"
            using trigger_res_1
            by (meson atLeastLessThan_iff not_le_imp_less)
          moreover have "maskL = join_mask (args_n args) (args_L args)"
            using assms(1)
            by auto
          ultimately have "tuple \<in> snd (trigger_results args mt auxlist)"
            using non_empty wf
            unfolding relL_def
            by fastforce
        }
        ultimately have "tuple \<in> snd (trigger_results args mt auxlist)"
          by blast
      }
      ultimately have "tuple \<in> snd (trigger_results args mt auxlist)"
        using hist_sat_mem
        by blast
      then have "tuple \<in> snd (trigger_results args cur auxlist)"
        using time
        by auto
    }
    then have subset: "snd (result_mmtaux args aux) \<subseteq> snd (trigger_results args cur auxlist)"
      by blast
    {
      fix tuple
      assume el: "tuple \<in> snd (trigger_results args cur auxlist)"
      then have wf: "wf_tuple (args_n args) (args_R args) tuple"
        using non_empty_alt
        by auto
      have maskL: "maskL = join_mask (args_n args) (args_L args)"
        using assms(1)
        by auto
      then have "(\<forall>i \<in> {0..<(length auxlist)}.
          let (t, l, r) = auxlist!i in
          mem (args_ivl args) (cur - t) \<longrightarrow> 
          (
            tuple \<in> r \<or>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
            )
          )
        )"
        using el non_empty_alt
        unfolding relL_def
        by fastforce
      then have tuple_props: "(\<forall>i \<in> {0..<(length auxlist)}.
          mem (args_ivl args) (cur - time (auxlist!i)) \<longrightarrow> 
          (
            tuple \<in> relR (auxlist!i) \<or>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
            )
          )
        )"
        using el
        unfolding relR_def time_def
        by (fastforce simp add: Let_def)
      {
        assume hist: "\<forall>i \<in> {0..<(length auxlist)}.
          mem (args_ivl args) (cur - time (auxlist!i)) \<longrightarrow> tuple \<in> relR (auxlist!i)"
        {
          fix db
          assume "db \<in> set (auxlist_data_in args mt auxlist)"
          then have db_props: "mem (args_ivl args) (cur - time db)" "db \<in> set auxlist"
            using time
            unfolding auxlist_data_in_def time_def
            by auto
          from db_props(2) obtain j where j_props:
              "j \<in> {0..<(length auxlist)}"
              "db = auxlist!j"
            by (metis atLeastLessThan_iff in_set_conv_nth leI not_less0)
          then have "tuple \<in> relR db"
            using hist db_props j_props
            by auto
        }
        then have "\<forall>db \<in> set (auxlist_data_in args mt auxlist). tuple \<in> relR db"
          by auto
        then have "\<forall>(t, r) \<in> set (map (\<lambda>(t, l, r). (t, r)) (auxlist_data_in args mt auxlist)). tuple \<in> r"
          unfolding relR_def
          by auto
        moreover have "(\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
          (\<not>is_empty data_in) \<and> (
            \<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r
        ))" using assms(1) by auto
        ultimately have "tuple \<in> hist_sat"
          using non_empty_alt
          by auto
        then have "tuple \<in> snd (result_mmtaux args aux)"
          using non_empty_alt
          unfolding aux_def
          by auto
      }
      moreover {
        assume "\<exists>i \<in> {0..<(length auxlist)}.
          mem (args_ivl args) (cur - time (auxlist!i)) \<and> tuple \<notin> relR (auxlist!i)"      
        then obtain i where i_props:
          "i \<in> {0..<(length auxlist)}"
          "mem (args_ivl args) (cur - time (auxlist!i))"
          "tuple \<notin> relR (auxlist!i)"
          by auto
  
        define A where "A = {j \<in> {i<..<(length auxlist)}. join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)}"
        define j where "j = Max A"
  
        have "\<exists>j \<in> {i<..<(length auxlist)}.
          join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
        "
          using i_props el tuple_props
          unfolding time_def relR_def
          by fastforce
        then have A_props: "A \<noteq> {}" "finite A" unfolding A_def by auto
        then have "j \<in> A" unfolding j_def by auto
        then have j_props:
          "j \<in> {i<..<(length auxlist)}"
          "join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)"
          using A_def
          by auto
  
        {
          define suffix where "suffix = drop j (auxlist_data_in args mt auxlist)"
          assume j_le: "j < length (linearize data_in)"
          (* length (auxlist_data_in args mt auxlist)-1 *)
          moreover have data_in_props: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
            using assms(1)
            by auto
          ultimately have "hd suffix = auxlist!j"
            using data_props(2)
            unfolding suffix_def
            by (metis (no_types, lifting) hd_drop_conv_nth length_map nth_take)
          
  
          then have suffix_first: "join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)"
            using j_props
            by auto
  
          have "length (auxlist_data_in args mt auxlist) = length (linearize data_in)"
            using data_props(2)
            by (metis length_map)
          then have j_le: "j < length (auxlist_data_in args mt auxlist)"
            using j_le
            by auto
  
          {
            fix db
            assume suffix_mem: "db \<in> set suffix"
            then obtain k where k_props:
              "k \<in> {0..<length suffix}"
              "suffix!k = db"
              by (meson atLeastLessThan_iff less_eq_nat.simps(1) nth_the_index the_index_bounded)
            then have kj_props:
              "(k+j) \<in> {0..<length (auxlist_data_in args mt auxlist)}"
              "(auxlist_data_in args mt auxlist)!(k+j) = db"
              using suffix_def
              by (auto simp add: add.commute)
            then have "(k+j) \<in> {0..<length auxlist}"
              unfolding auxlist_data_in_def
              by (simp add: less_le_trans)
  
            then have cond: "
              mem (args_ivl args) (cur - time (auxlist!(k+j))) \<longrightarrow> 
              (
                tuple \<in> relR (auxlist!(k+j)) \<or>
                (\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                  join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
                )
              )" using tuple_props by auto
  
  
            have "db \<in> set (auxlist_data_in args mt auxlist)"
              using kj_props
              by auto
            then have "mem (args_ivl args) (cur - time db)"
              using time
              unfolding auxlist_data_in_def time_def
              by auto
            moreover have auxlist_idx: "(auxlist_data_in args mt auxlist)!(k+j) = auxlist!(k+j)"
              using data_in_props kj_props(1)
              by auto
            ultimately have "mem (args_ivl args) (cur - time (auxlist!(k+j)))"
              using kj_props(2)
              by auto
            
            then have "tuple \<in> relR (auxlist!(k+j)) \<or>
                (\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                  join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
                )"
              using cond
              by auto
  
            moreover {
              assume "(\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                  join_cond (args_pos args) (relL (auxlist!j)) (proj_tuple maskL tuple)
                )"
              then obtain j' where j'_props:
                "j' \<in> {(k+j)<..<(length auxlist)}"
                "join_cond (args_pos args) (relL (auxlist!j')) (proj_tuple maskL tuple)"
                by blast
  
              then have "j' \<in> A" using A_def j_props by auto
              then have "j' \<le> j" using A_props j_def by auto
              then have "False" using j'_props by auto
            }
  
            ultimately have "tuple \<in> relR (auxlist!(k+j))" by blast
            then have "tuple \<in> relR db" using kj_props auxlist_idx by auto
          }
          then have "(\<forall>(t, l, r) \<in> set suffix.
                tuple \<in> r
              )"
              "join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)"
            using suffix_first
            unfolding relR_def
            by (auto simp add: relR_def case_prod_beta')
          then have "\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
            let suffix = drop n (auxlist_data_in args mt auxlist) in (
              (\<forall>(t, l, r) \<in> set suffix.
                tuple \<in> r
              ) \<and>
              join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)
          )"
            using j_le suffix_def
            by (meson atLeastLessThan_iff less_eq_nat.simps(1))
          then have "(\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
                let suffix = drop n (auxlist_data_in args mt auxlist) in (
                  (\<forall>(t, l, r) \<in> set suffix.
                    tuple \<in> r
                  ) \<and>
                  (
                    join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)
                  )
              )
            )"
            by (auto simp add: Let_def)
          moreover have "length (linearize data_in) = length (auxlist_data_in args mt auxlist)"
          proof -
            have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
              using assms(1)
              by auto
            then show ?thesis
              by (metis length_map)
          qed
          ultimately have "tuple_since_lhs tuple (linearize data_in) args maskL (auxlist_data_in args mt auxlist)"
            using non_empty_alt is_empty_alt
            unfolding tuple_since_lhs_def 
            by auto
          then have "tuple \<in> since_sat" using assms(1) by auto
          then have "tuple \<in> snd (result_mmtaux args aux)"
            using non_empty_alt
            unfolding aux_def
            by auto
        }
        moreover {
          define j' where "j' = j - length (linearize data_in)"
          assume j_geq: "j \<ge> length (linearize data_in)"
          moreover have data_prev_props: "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
            using assms(1)
            by auto
          ultimately have prev: "auxlist!j = (auxlist_data_prev args mt auxlist)!j'"
            using j_props(1)
            unfolding j'_def
            by auto
          then have idx_shift: "auxlist!j = (linearize data_prev)!j'"
            using data_props(1)
            by auto
          have "j' < length (auxlist_data_prev args mt auxlist)"
            using data_prev_props j_props i_props j_geq
            unfolding j'_def
            by auto
          then have not_mem_0: "\<not>mem (args_ivl args) 0"
            using memL_mono[of "args_ivl args" 0]
            unfolding auxlist_data_prev_def
            by auto
          then have mask_eq: "(args_L args) = (args_R args)"
            using assms(1)
            by auto
  
          have data_in_props: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
            using assms(1)
            by auto
          have "length (linearize data_prev) + length (linearize data_in) = length auxlist"
            using data_in_props data_prev_props data_props
            by (smt add.commute append_take_drop_id length_append length_map)
          then have j'_le: "j' < length (linearize data_prev)"
            using j_geq j_props(1)
            unfolding j'_def
            by auto
          
          define B where "B = fst ` {
            tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
            tuple = snd tas
          }"
          from assms(1) have "newest_tuple_in_mapping fst data_prev tuple_in_once (\<lambda>x. True)"
            by auto
          then have mapping_val: "Mapping.lookup tuple_in_once tuple = safe_max B"
            unfolding newest_tuple_in_mapping_def B_def
            by auto
  
          define t where "t = fst ((linearize data_prev) ! j')"
          define X where "X = snd ((linearize data_prev) ! j')"
          have tuple_eq: "proj_tuple maskL tuple = tuple"
            using mask_eq wf wf_tuple_proj_idle[of "args_n args" "args_L args" tuple] maskL
            by auto
          have "args_pos args"
            using not_mem_0 assms(1)
            by auto
          then have "proj_tuple maskL tuple \<in> fst X"
            using j_props idx_shift
            unfolding relL_def X_def
            by auto
          moreover have
            "(t, X) \<in> (set (linearize data_prev))"
            using j'_le
            unfolding t_def X_def
            by auto
          ultimately have "(t, proj_tuple maskL tuple) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev))"
            unfolding ts_tuple_rel_f_def
            by blast
          then have t_mem_B: "t \<in> B"
            unfolding B_def
            using tuple_eq
            by (simp add: image_iff)
          then have B_props: "B \<noteq> {}" "finite B"
            using B_def
            by (auto simp add: finite_fst_ts_tuple_rel)
          then have "safe_max B = Some (Max B)"
            unfolding safe_max_def
            by auto
          then have "Mapping.lookup tuple_in_once tuple = Some (Max B)"
            using mapping_val
            by auto
          then have "tuple \<in> Mapping.keys tuple_in_once"
            by (simp add: Mapping_keys_intro)
          moreover have "tuple_in_once_keys = Mapping.keys tuple_in_once"
            using assms(1)
            by auto
          ultimately have "tuple \<in> snd (result_mmtaux args aux)"
            using non_empty_alt
            unfolding aux_def
            by auto
        }
        ultimately have "tuple \<in> snd (result_mmtaux args aux)" using not_le_imp_less by blast
      }
      ultimately have "tuple \<in> snd (result_mmtaux args aux)" by blast
    }
    then have "snd (trigger_results args cur auxlist) \<subseteq> snd (result_mmtaux args aux)"
      by auto
    then have "snd (trigger_results args cur auxlist) = snd (result_mmtaux args aux)"
      using subset
      by blast
    then have ?thesis using aux_def non_empty_alt by auto
  }
  moreover {
    assume "is_empty data_in"
    then have ?thesis using data_in_auxlist_nonempty[OF assms(1)] time by auto
  }
  ultimately show ?thesis by blast
qed

lemma valid_result_mmtaux: "valid_mmtaux args cur aux auxlist \<Longrightarrow> result_mmtaux args aux = trigger_results args cur auxlist"
  using valid_result_mmtaux_unfolded
  by (cases aux) (fast)

lemma drop_list_shift: "n \<ge> m \<Longrightarrow> drop n xs = drop (n - m) (drop m xs)"
  by simp

(* analogous to join_mmsaux *)
fun proj_tuple_in_join_optim :: "bool \<Rightarrow> 'a table \<Rightarrow> bool list \<Rightarrow> 'a table \<Rightarrow> bool list \<Rightarrow> 'a table" where
  "proj_tuple_in_join_optim pos r maskR l maskL = (
    if maskL = maskR then (
      if pos then r \<inter> l else r - l 
    )
    else if (\<forall>b \<in> set maskL. \<not>b) then (
      let nones = replicate (length maskL) None in (
      \<comment> \<open>if there are no free variables then we either take all or nothing\<close>
        if pos \<longleftrightarrow> nones \<in> l then
          r
         else
          {}
        )
      )
    else
      {as \<in> r. proj_tuple_in_join pos maskL as l}
    )"

lemma proj_tuple_in_join_optim_equiv:
  assumes "table n V_L l"
  assumes "table n V_R r"
  shows "proj_tuple_in_join_optim pos r (join_mask n V_R) l (join_mask n V_L) =
         {as \<in> r. proj_tuple_in_join pos (join_mask n V_L) as l}"
proof -
  define maskL where "maskL = (join_mask n V_L)"
  define maskR where "maskR = (join_mask n V_R)"
  have maskL_len: "length (maskL) = n"
    unfolding maskL_def join_mask_def
    by auto

  show ?thesis
  proof (cases "maskL = maskR")
    case True
    then have "\<And>as. as \<in> r \<Longrightarrow> proj_tuple maskL as = as"
      using wf_tuple_proj_idle assms(2)
      unfolding table_def maskR_def
      by auto
    then have "{as \<in> r. proj_tuple_in_join pos (join_mask n V_L) as l} =
               {as \<in> r. join_cond pos l as}"
      unfolding proj_tuple_in_join_def maskL_def
      by auto
    then show ?thesis
      using True
      unfolding maskL_def maskR_def
      by auto
next
  case not_eq: False
  then show ?thesis
  proof (cases "(\<forall>b \<in> set maskL. \<not>b)")
    case no_fvs: True
    then have "\<forall>i<n. i \<notin> V_L"
      unfolding maskL_def join_mask_def
      by auto
    then have "\<forall>x\<in>l. x = replicate n None"
      using assms(1)
      unfolding table_def wf_tuple_def
      by (simp add: New_max.simple_list_index_equality)
    then have l_eq: "l = {} \<or> l = unit_table n"
      using assms(1)
      unfolding unit_table_def
      by auto
    then show ?thesis
    proof (cases "pos \<longleftrightarrow> (replicate (length maskL) None) \<in> l")
      case True
      {
        assume assm: "\<not>pos"
        then have "replicate n None \<notin> l"
          using True maskL_len
          by auto
        then have "l = {}"
          using l_eq
          unfolding unit_table_def
          by auto
        then have "{as \<in> r. proj_tuple_in_join pos maskL as l} = r"
          using no_fvs assm
          unfolding proj_tuple_in_join_def
          by auto
      }
      moreover {
        assume assm: "pos"
        then have l_eq: "l = unit_table n"
          using True maskL_len l_eq
          by auto
        
        have as_props: "\<And>as. as \<in> r \<Longrightarrow> length as = n"
          using assms(2)
          unfolding table_def wf_tuple_def
          by auto
        have "\<And>as. as \<in> r \<Longrightarrow> proj_tuple maskL as = replicate n None"
        proof -
          fix as
          assume "as \<in> r"
          then have "length as = n"
            using as_props
            by auto
          then have len_eq: "length maskL = length as"
            using maskL_len
            by auto
          show "proj_tuple maskL as = replicate n None"
            using no_fvs proj_tuple_replicate[OF _ len_eq] maskL_len
            by auto
        qed
        then have "\<And>as. as \<in> r \<Longrightarrow> proj_tuple maskL as \<in> l"
          unfolding l_eq unit_table_def
          by auto
        then have "{as \<in> r. proj_tuple_in_join pos maskL as l} = r"
          using assm
          unfolding proj_tuple_in_join_def
          by auto
      }
      ultimately have "{as \<in> r. proj_tuple_in_join pos maskL as l} = r"
        by blast

      moreover have "proj_tuple_in_join_optim pos r (join_mask n V_R) l (join_mask n V_L) = r"
        using not_eq no_fvs True
        unfolding maskL_def maskR_def proj_tuple_in_join_optim.simps Let_def
        by auto

      ultimately show ?thesis
        unfolding maskL_def
        by auto
    next
      case False
      {
        assume assm: "pos"
        then have "replicate n None \<notin> l"
          using False maskL_len
          by auto
        then have "l = {}"
          using l_eq
          unfolding unit_table_def
          by auto
        then have "{as \<in> r. proj_tuple_in_join pos maskL as l} = {}"
          using no_fvs assm
          unfolding proj_tuple_in_join_def
          by auto
      }
      moreover {
        assume assm: "\<not>pos"
        then have l_eq: "l = unit_table n"
          using False maskL_len l_eq
          by auto
        
        have as_props: "\<And>as. as \<in> r \<Longrightarrow> length as = n"
          using assms(2)
          unfolding table_def wf_tuple_def
          by auto
        have "\<And>as. as \<in> r \<Longrightarrow> proj_tuple maskL as = replicate n None"
        proof -
          fix as
          assume "as \<in> r"
          then have "length as = n"
            using as_props
            by auto
          then have len_eq: "length maskL = length as"
            using maskL_len
            by auto
          show "proj_tuple maskL as = replicate n None"
            using no_fvs proj_tuple_replicate[OF _ len_eq] maskL_len
            by auto
        qed
        then have "\<And>as. as \<in> r \<Longrightarrow> proj_tuple maskL as \<in> l"
          unfolding l_eq unit_table_def
          by auto
        then have "{as \<in> r. proj_tuple_in_join pos maskL as l} = {}"
          using assm
          unfolding proj_tuple_in_join_def
          by auto
      }
      ultimately have "{as \<in> r. proj_tuple_in_join pos maskL as l} = {}"
        by blast

      moreover have "proj_tuple_in_join_optim pos r (join_mask n V_R) l (join_mask n V_L) = {}"
        using not_eq no_fvs False
        unfolding maskL_def maskR_def proj_tuple_in_join_optim.simps Let_def
        by auto
      
      ultimately show ?thesis
        unfolding maskL_def
        by auto
    qed
  next
    case False
    then show ?thesis
      using not_eq
      unfolding maskL_def maskR_def
      by auto
  qed
qed
qed

fun update_mmtaux' :: "args \<Rightarrow> ts \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue \<Rightarrow> (ts \<times> 'a table) queue \<Rightarrow> (('a tuple, ts) mapping) \<Rightarrow> 'a table \<Rightarrow> (('a tuple, nat) mapping) \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> (nat \<times> nat \<times> (ts \<times> 'a table \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times> (('a tuple, ts) mapping) \<times> 'a table \<times> (('a tuple, nat) mapping) \<times> 'a table \<times> 'a table)" where
  "update_mmtaux' args nt idx_mid idx_oldest maskL maskR data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat = (
    \<comment> \<open>in a first step, we update tuple_in_once by removing all tuples where currently a ts
       is stored, that points to a db that with the new ts (nt) no longer is part of
       [0, a-1] / data_prev\<close>
    let (_, data_prev', move, tuple_in_once', tuple_in_once_keys') = shift_end
      (flip_int_less_lower (args_ivl args)) \<comment> \<open>[0, a-1]\<close>
      nt  \<comment> \<open>the new timestamp\<close>
      fst \<comment> \<open>here we look at the lhs tuples / \<phi>\<close>
      (empty_queue::(ts \<times> 'a option list set \<times> 'a option list set) queue, data_prev, tuple_in_once, tuple_in_once_keys); \<comment> \<open>add type\<close>
    \<comment> \<open>pass empty_queue as the first argument as it would filter out all: [0, a-1] \<inter> [a, b] = {}.
       idx_mid can be moved forward by the number of all tuples dropped from data_prev (move)\<close>
    move_len = length move;
    idx_mid' = idx_mid + move_len;
    \<comment> \<open>in a next step, we drop all entries from data_in that are no longer relevant \<close>
    (data_in', drop) = takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in;
     \<comment> \<open>instead of first appending and then filtering, we filter move separately. this saves us the append
       operation for all entries in move\<close>
    move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move;
    \<comment> \<open>idx_ildest has to be moved forward by the number of dbs dropped from data_in and the ones
        dropped from data_prev because they don't satisfy memR anymore (move')\<close>
    drop_prev_len = move_len - length move';
    idx_oldest' = idx_oldest + length drop + drop_prev_len;
    
    \<comment> \<open>next, the right hand side of entries in move have to be appended to data_in. these all already
       satisfy memR as we just filtered them for it\<close>
    data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in';
    
    \<comment> \<open>we now have to update hist_since using the tables in move. in particular, for all dbs inside move,
       we have to do some sort of join with the keys of hist_since\<close>
    (tuple_since_hist', hist_sat', idx_move, since_sat') = fold (\<lambda>(t, l, r) (tuple_since_hist, hist_sat, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat         = hist_sat \<inter> r;
          since_sat        = since_sat \<inter> r

      in \<comment> \<open>filter entries that are not present in the current db\<close>
      (
        upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist), \<comment> \<open>then add entries for the ones that are present in the current db\<close>
        hist_sat,
        idx_move+1, \<comment> \<open>increase index by one every db\<close>
        since_sat \<union> proj_tuple_in_join_optim (args_pos args) r (join_mask (args_n args) (args_R args)) l (join_mask (args_n args) (args_L args))
      ) 
    ) move (tuple_since_hist, hist_sat, idx_mid, since_sat); \<comment> \<open>use original idx_mid, not idx_mid' where the length of move already is included\<close>
    tuple_since_hist'' = (if (idx_mid' = idx_oldest') then Mapping.empty else tuple_since_hist'); \<comment> \<open>if data_in'' is empty, empty the mapping\<close>
    since_sat'' = (if (idx_mid' = idx_oldest') then {} else since_sat');
    \<comment> \<open>in contrast to mmsaux, we don't have to look at what tuples were dropped from data_in as
       we do not have any 'in mappings', just 'since mappings'. What has to be done though,
       is to check whether there are now new tuples that satisfy historically.
       In order to do this, we look at the latest db, iterate over all tuples and check,
       whether hist_since points to an index that is older than the current oldest ts, i.e.
       whether the rhs is satisfied in the whole interval\<close>
    hist_sat'' = (case fst (safe_hd data_in'')
      of None \<Rightarrow>
        {} \<comment> \<open>if data_in is empty, no tuples should be in the set.
              (mmtaux only returns results if data_in isn't empty)\<close>
      | Some db \<Rightarrow>
        \<comment> \<open>select all tuples where tuple_since_hist points to the smallest ts\<close>
        hist_sat' \<union> {tuple \<in> (snd db).
          case (Mapping.lookup tuple_since_hist'' tuple) of
            Some idx \<Rightarrow> idx \<le> idx_oldest'
          | None \<Rightarrow> False
        }
    )
    in
    (idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys', tuple_since_hist'', hist_sat'', since_sat'')
  )"


lemma ts_tuple_rel_empty: "ts_tuple_rel_f (\<lambda>_. {}) A = {}"
  unfolding ts_tuple_rel_f_def
  by auto

lemma Mapping_empty_filter: "Mapping.filter f Mapping.empty = Mapping.empty"
  by (metis Mapping.lookup_empty Mapping_lookup_filter_not_None mapping_eqI)

lemma fold_Mapping_filter_empty: "fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs Mapping.empty = Mapping.empty"
proof (induction xs arbitrary: )
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs Mapping.empty) = Mapping.empty"
    by auto
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs (Mapping.filter (f x Mapping.empty) Mapping.empty)) = Mapping.empty"
    using Mapping_empty_filter[of "f x Mapping.empty"]
    by auto
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs \<circ> (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) x) Mapping.empty = Mapping.empty"
    by auto
  then show ?case by simp
qed

lemma Mapping_filter_Some:
  assumes "Mapping.lookup mapping k = Some v"
  assumes "f k v = True"
  shows "Mapping.lookup (Mapping.filter f mapping) k = Some v"
  using assms
  by (simp add: Mapping_keys_filterI Mapping_lookup_filter_keys)

lemma Mapping_filter_None:
  assumes "Mapping.lookup mapping k = None"
  shows "Mapping.lookup (Mapping.filter f mapping) k = None"
  using assms Mapping_lookup_filter_not_None
  by fastforce

lemma restrict_double_appl: "restrict M t = restrict M (restrict M t)"
  by (auto simp: restrict_def)

lemma filter_order_inv: "filter f (filter g xs) = filter g (filter f xs)"
  by (metis (mono_tags, lifting) filter_cong filter_filter)

lemma not_memL_imp_memR: "\<not> memL (args_ivl args) t \<Longrightarrow> memR (args_ivl args) t"
proof -
  assume "\<not> memL (args_ivl args) t"
  then have memL: "\<forall>t'\<le>t. \<not>mem (args_ivl args) t'" using memL_mono by auto
  have "(memL (args_ivl args), memR (args_ivl args), bounded (args_ivl args)) \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using Rep_\<I>[of "(args_ivl args)"]
    by (simp add: bounded.rep_eq memL.rep_eq memR.rep_eq)
  then obtain t_ex where t_ex_props: "mem (args_ivl args) t_ex"
    by auto
  {
    assume memR: "\<not>memR (args_ivl args) t"
    {
      fix t'
      assume t'_leq_t: "t' \<ge> t"
      then have "\<not>memR (args_ivl args) t'"
        using memR memR_antimono
        by auto
    }
    then have "\<forall>t'\<ge>t. \<not>mem (args_ivl args) t'" by auto
    then have "\<forall>t'. \<not>mem (args_ivl args) t'"
      using memL nat_le_linear
      by auto
    then have "False" using t_ex_props by auto
  }
  then show "memR (args_ivl args) t" by auto
qed

lemma not_memR_imp_memL: "\<not> memR (args_ivl args) t \<Longrightarrow> memL (args_ivl args) t"
proof -
  assume "\<not> memR (args_ivl args) t"
  then have memR: "\<forall>t'\<ge>t. \<not>memR (args_ivl args) t'" using memR_antimono by auto
  have "(memL (args_ivl args), memR (args_ivl args), bounded (args_ivl args)) \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using Rep_\<I>[of "(args_ivl args)"]
    by (simp add: bounded.rep_eq memL.rep_eq memR.rep_eq)
  then obtain t_ex where t_ex_props: "mem (args_ivl args) t_ex"
    by auto
  {
    assume memL: "\<not>memL (args_ivl args) t"
    {
      fix t'
      assume t'_leq_t: "t' \<le> t"
      then have "\<not>memL (args_ivl args) t'"
        using memL memL_mono
        by auto
    }
    then have "\<forall>t'\<le>t. \<not>mem (args_ivl args) t'" by auto
    then have "\<forall>t'. \<not>mem (args_ivl args) t'"
      using memR nat_le_linear
      by auto
    then have "False" using t_ex_props by auto
  }
  then show "memL (args_ivl args) t" by auto
qed

lemma fold_append_queue_map: "linearize (fold (\<lambda>(t, l, r) q. append_queue (t, r) q) xs q) = linearize q @ (map (\<lambda>(t, l, r). (t, r)) xs)"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

lemma filter_imp: "(\<forall>x. P x \<longrightarrow> Q x) \<longrightarrow> length (filter P xs) \<le> length (filter Q xs)"
  by (metis (mono_tags, lifting) filter_cong filter_filter length_filter_le)

lemma filter_take_drop:
  assumes "filter P xs = take n xs"
  shows "filter (\<lambda>x. \<not> P x) xs = drop n xs"
  using assms apply (induction xs arbitrary: n)
   apply (auto)
  subgoal for a xs n
    apply (cases n)
     apply (auto simp add: filter_empty_conv filter_eq_Cons_iff)
    done
  subgoal for a xs n
    apply (cases n)
     apply (auto simp add: filter_empty_conv filter_eq_Cons_iff)
    done
  done

lemma mem_mt_and_memR_imp_mem:
  assumes "nt \<ge> mt"
  shows "(mem (args_ivl args) (mt - t) \<and> memR (args_ivl args) (nt - t)) = (mem (args_ivl args) (mt - t) \<and> mem (args_ivl args) (nt - t))"
  using assms by auto

lemma take_filter_mem:
  assumes "\<forall>db \<in> set xs. memR I (mt - time db)"
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). mem I (mt - t)) xs = take (length (filter (\<lambda>(t, _). mem I (mt - t)) xs)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). mem I (mt - t)) xs = take (length (filter (\<lambda>(t, _). mem I (mt - t)) xs)) xs"
    using Cons
    by auto
  from Cons(2) have x_memR: "((\<lambda>(t, _). memR I (mt - t)) x)" unfolding time_def by auto
  show ?case
  proof (cases "(\<lambda>(t, _). mem I (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). mem I (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). mem I (mt - t)) xs)"
      by auto
    moreover have "take (length (filter (\<lambda>(t, _). mem I (mt - t)) (x#xs))) (x#xs) = x#(take (length (filter (\<lambda>(t, _). mem I (mt - t)) xs)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). mem I (mt - t)) (x#xs) = (filter (\<lambda>(t, _). mem I (mt - t)) xs)"
      by auto
    then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). mem I (mt - t)) (x#xs))) (x#xs) = take (length (filter (\<lambda>(t, _). mem I (mt - t)) xs)) (x#xs)"
      by auto
    show ?thesis
    proof (cases "length (filter (\<lambda>(t, _). mem I (mt - t)) xs)")
      case 0
      then show ?thesis by auto
    next
      case (Suc nat)
      then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). mem I (mt - t)) (x#xs))) (x#xs) = x # (take nat xs)"
        using takeWhile_IH
        by auto
      then show ?thesis
      proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). \<not>mem I (mt - t)) db")
        case True
        then have "filter (\<lambda>(t, _). mem I (mt - t)) (x#xs) = []"
          using filter_IH
          by (simp add: case_prod_beta')
        then show ?thesis using takeWhile_IH by auto
      next
        case False
        then obtain j where j_props: "((\<lambda>(t, _). mem I (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
          by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
        then have "((\<lambda>(t, _). mem I (mt - t)) ((x#xs)!(Suc j)))"
          by auto
        moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
          using Cons(3) j_props
          by auto
        ultimately have "((\<lambda>(t, _). mem I (mt - t)) x)" using x_memR by auto
        then show ?thesis using not_mem by auto
      qed
    qed
  qed
qed


lemma fold_alt: "fold f (xs @ [x]) acc = f x (fold f xs acc)"
  by simp

lemma drop_last: "length xs \<ge> 1 \<Longrightarrow> drop (length xs - 1) xs = [last xs]"
  by (smt One_nat_def append_butlast_last_id append_eq_append_conv append_take_drop_id diff_diff_cancel diff_is_0_eq' le_add_diff_inverse le_numeral_extra(4) length_drop length_greater_0_conv length_nth_simps(1) list.size(4) zero_le_one)

lemma filter_sublist: "x#xs = filter f zs \<Longrightarrow> \<exists>n\<le>length zs. xs = filter f (drop n zs) \<and> [x] = filter f (take n zs)"
  proof (induction zs)
    case (Cons z zs)
    then show ?case
    proof (cases "f z")
      case False
      then obtain n where "n\<le>length zs" "xs = filter f (drop n zs)" "[x] = filter f (take n zs)"
        using Cons
        by auto
      then show ?thesis
        using False
        by (auto intro: exI[of _ "n+1"])
    qed (auto intro: exI[of _ 1])
  qed (auto)

lemma idx_filter:
  assumes "x = (filter f xs)!i"
  assumes "i < length (filter f xs)"
  shows "\<exists>i' \<in> {0..<length xs}. xs!i' = x"
  using assms
  by (metis (full_types) Set.member_filter atLeastLessThan_iff filter_set in_set_conv_nth zero_le)

lemma idx_filter_pair:
  assumes "x = (filter f xs)!i"
  assumes "y = (filter f xs)!j"
  assumes "j < i" "i < length (filter f xs)"
  shows "\<exists>i' \<in> {0..<length xs}. \<exists>j' \<in> {0..<i'}. xs!j' = y \<and> xs!i' = x"
using assms proof (induction "filter f xs" arbitrary: xs i j)
  case (Cons a as zs)

  obtain i' where i'_def: "i = Suc i'"
    using Suc Cons(5)
    by (cases i) (auto)

  obtain n where zs'_props: "n\<le>length zs" "as = filter f (drop n zs)" "[a] = filter f (take n zs)"
    using Cons filter_sublist[of a as f zs]
    by auto

  show ?case
  proof (cases j)
    case 0

    obtain i'' where i''_props: "i'' \<in> {0..<length (drop n zs)}" "(drop n zs)!i'' = x"
      using idx_filter[of x f "(drop n zs)" i'] Cons(3-)[folded Cons(2)] zs'_props
      by (auto simp add: i'_def)

    have "y = a" using 0 Cons(2)[symmetric] Cons(4) by auto
    then have y_list: "[y] = filter f (take n zs)" using zs'_props(3) by auto
    then have "filter f (take n zs)!0 = y"
      by (metis nth_Cons_0)
    moreover have "0 < length (filter f (take n zs))" using y_list by auto

    ultimately obtain j'' where j''_props: "j'' \<in> {0..<length (take n zs)}" "(take n zs)!j'' = y"
      using idx_filter[of y f "(take n zs)" 0]
      by (auto)

    show ?thesis
      apply (rule bexI[of _ "n + i''"])
       using i''_props j''_props
       by (auto intro!: bexI[of _ "j''"])
      
  next
    case (Suc j')

    show ?thesis
      using Cons(1)[OF zs'_props(2), folded zs'_props(2), of i' j'] Cons(3-)[folded Cons(2)]
      apply (auto simp: Suc i'_def)
      subgoal for i'' j''
        by (rule bexI[of _ "n + i''"]) auto
      done
  qed
qed (simp)

lemma no_hist_last_not_sat:
  assumes data_in_len: "length xs + idx_oldest = idx_mid"
  assumes tuple_since_tp: "\<forall>idx. \<not> tuple_since_tp args as xs idx_oldest idx_mid idx"
  assumes non_empty: "xs \<noteq> []"
  shows "as \<notin> snd (last xs)"
proof -
  have idx_props: "\<forall>idx<idx_mid. (
      \<not>(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) xs). 
        as \<in> r
      ) \<or>
      \<not>(idx > idx_oldest \<longrightarrow> as \<notin> (snd (xs!(idx-idx_oldest-1))))
    )"
    using tuple_since_tp non_empty
    unfolding tuple_since_tp_def
    by auto
  {
    define db where "db = last xs"
    define i where "i = length xs - 1"
    assume assm: "as \<in> snd db"
    then have in_len: "length xs > 0"
      using non_empty by auto
    then have db_i: "db = xs!i"
      unfolding db_def i_def
      using last_conv_nth
      by blast
    define A where "A = {j \<in> {0..<length xs}. as \<notin> snd (xs!j)}"
    define j where "j = Max A"
    define idx where "idx = idx_oldest + j + 1"
    {
      define idx where "idx = idx_oldest"
      assume hist: "\<forall>db \<in> set xs. as \<in> snd db"
      have "idx < idx_mid" "\<forall>(t, r) \<in> set (drop (idx-idx_oldest) xs). as \<in> r"
        unfolding idx_def
        using data_in_len in_len hist
        by auto
      moreover have "idx > idx_oldest \<longrightarrow> as \<notin> (snd (xs!(idx-idx_oldest-1)))"
        unfolding idx_def
        by blast
      ultimately have "False"
        using idx_props assm(1)
        by auto
    }
    then obtain db' where db'_props: "db' \<in> set xs" "as \<notin> snd db'" by blast
    then have "\<exists>j. xs!j = db' \<and> j \<in> {0..<length xs}"
      by (meson atLeastLessThan_iff leI not_less0 nth_the_index the_index_bounded)
    then have A_props: "A \<noteq> {}" "finite A"
      unfolding A_def
      using db'_props(2)
      by auto
    then have "j \<in> A"
      unfolding j_def
      by auto
    then have j_props: "j \<in> {0..<length xs}" "as \<notin> snd (xs!j)"
      unfolding A_def
      by auto
    then have j_le_i: "j \<in> {0..<i}"
      using db_i assm
      unfolding i_def
      by (metis One_nat_def Suc_leI Suc_pred atLeastLessThan_iff in_len leD linorder_neqE_nat)
    {
      assume "\<exists>k \<in> {j<..<length xs}. as \<notin> snd (xs!k)"
      then obtain k where k_props: "k \<in> {j<..<length xs}" "as \<notin> snd (xs!k)"
        by auto
      then have "k \<in> A" unfolding A_def by auto
      then have "False" using k_props(1) A_props j_def by auto
    }
    then have suffix_hist: "\<forall>k \<in> {j<..<length xs}. as \<in> snd (xs!k)"
      by blast
    {
      fix db
      assume "db \<in> set (drop (j+1) xs)"
      then obtain k where k_props: "(drop (j+1) xs)!k = db" "k \<in> {0..<length (drop (j+1) xs)}"
        by (meson atLeastLessThan_iff in_set_conv_nth zero_le)
      then have "xs!(k + (j+1)) = db"
        by (simp add: add.commute)
      then have "as \<in> snd db" using suffix_hist
        using k_props(2)
        by auto
    }
    then have "\<forall>db \<in> set (drop (j+1) xs). as \<in> snd db"
      by auto
    then have "\<forall>(t, r) \<in> set (drop (idx-idx_oldest) xs). as \<in> r"
      unfolding idx_def
      by auto
    moreover have "as \<notin> (snd (xs!(idx-idx_oldest-1)))"
      unfolding idx_def
      using j_props(2)
      by auto
    moreover have "idx < idx_mid"
      using data_in_len j_le_i
      unfolding idx_def i_def
      by auto
    ultimately have "False"
      using idx_props assm(1)
      by auto
  }
  then show "as \<notin> snd (last xs)" by auto
qed

lemma idx_append_snd: "i \<in> {length ys..<length xs} \<Longrightarrow> xs = ys @ zs \<Longrightarrow> xs!i = zs!(i - length ys)"
  by (simp add: nth_append)

lemma nth_set_member: "i \<in> {0..<length xs} \<Longrightarrow> xs!i \<in> set xs"
  by auto

lemma tuple_since_hist_lookup_eq:
  assumes "(\<forall>as. (case Mapping.lookup tuple_since_hist as of
    Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx
    | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx)
  )"
  assumes "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid jdx" "jdx > idx_oldest"
  assumes "length (linearize data_in) + idx_oldest = idx_mid"
  shows "Mapping.lookup tuple_since_hist as = Some jdx"
proof -
  (* (idx_oldest + j + 1) = jdx *)
  define j where "j = jdx - idx_oldest - 1"

  from assms(2) have in_nonempty: "linearize data_in \<noteq> []"
    unfolding tuple_since_tp_def
    by auto

  from assms(2-3) have jdx_props: "jdx < idx_mid" "jdx > idx_oldest"
    unfolding tuple_since_tp_def
    by auto
  moreover have "as \<notin> snd ((linearize data_in)!j)"
    using assms(2) jdx_props(2)
    unfolding tuple_since_tp_def j_def
    by auto
  ultimately have j_props: "j \<in> {0..<length (linearize data_in) - 1}" "as \<notin> snd ((linearize data_in)!j)"
    using assms(4)
    unfolding j_def
    by auto

  from assms(2) have all_relR: "(\<forall>(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) (linearize data_in)). as \<in> y)"
    using jdx_props(2)
    unfolding tuple_since_tp_def j_def
    by fastforce

  obtain idx where idx_props:
    "Mapping.lookup tuple_since_hist as = Some idx"
    "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
    using assms(1) assms(2)
    by (auto split: option.splits)
  then have idx_l: "idx < idx_mid"
    unfolding tuple_since_tp_def
    by auto
  {
    assume assm: "idx < (idx_oldest + j + 1)"
    then have j_th: "(linearize data_in)!j = (drop (idx - idx_oldest) (linearize data_in))!(j - (idx - idx_oldest))"
      using idx_props(2) j_props(1) assms(4)
      unfolding tuple_since_tp_def
      by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right add_diff_cancel_left' add_diff_cancel_right' diff_Suc_Suc diff_le_mono le_add_diff_inverse less_imp_le_nat nth_drop)
    then have "(linearize data_in)!j \<in> set (drop (idx - idx_oldest) (linearize data_in))"
      using j_props(1) assm
      apply (cases "idx_oldest < idx")
       apply (auto)
      by (smt (verit) Suc_pred j_th add_diff_inverse_nat add_le_cancel_left add_less_cancel_left le_add1 le_less_trans le_simps(2) length_drop nat_diff_split_asm nth_mem zero_less_diff zero_order(3))
    moreover have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest) (linearize data_in)). as \<in> y)"
      using idx_props(2)
      unfolding tuple_since_tp_def
      by auto
    ultimately have "as \<in> snd ((linearize data_in)!j)" by auto
    then have "False" using j_props(2) by auto
  }
  moreover {
    assume assm: "idx > idx_oldest + j + 1"
    then have geq_drop: "idx - idx_oldest - 1 \<ge> j + 1"
      by auto
    moreover have l_len: "(idx - idx_oldest - 1) < length (linearize data_in)"
      using idx_l assms(4) in_nonempty assm
      by linarith
    ultimately have "linearize data_in ! (idx - idx_oldest - 1) = (drop (j + 1) (linearize data_in))!(idx - idx_oldest - 1 - j - 1)"
      by (smt diff_diff_left le_add_diff_inverse le_less_trans less_imp_le_nat nth_drop)
    then have "(linearize data_in ! (idx - idx_oldest - 1)) \<in> set (drop (j + 1) (linearize data_in))"
      by (metis (no_types, lifting) l_len geq_drop diff_diff_left diff_less_mono length_drop nth_mem)
    then have "as \<in> snd (linearize data_in ! (idx - idx_oldest - 1))"
      using all_relR
      by auto
    moreover have "as \<notin> snd (linearize data_in ! (idx - idx_oldest - 1))"
      using assm idx_props(2)
      unfolding tuple_since_tp_def
      by auto
    ultimately have "False" by auto
  }
  ultimately have "idx = (idx_oldest + j + 1)"
    using linorder_neqE_nat
    by blast
  then have "idx = jdx"
    using jdx_props
    unfolding j_def
    by auto
  then show ?thesis using idx_props(1) by auto
qed

lemma tuple_since_hist_lookup_leq:
  assumes "(case Mapping.lookup tuple_since_hist as of
    Some idx \<Rightarrow> tuple_since_tp args as lin_data_in idx_oldest idx_mid idx
    | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as lin_data_in idx_oldest idx_mid idx)
  "
  assumes "tuple_since_tp args as lin_data_in idx_oldest idx_mid idx_oldest"
  assumes "length lin_data_in + idx_oldest = idx_mid"
  shows "\<exists>idx. Mapping.lookup tuple_since_hist as = Some idx \<and> idx \<le> idx_oldest"
proof -
  {
    assume assm: "\<not>(\<exists>idx. Mapping.lookup tuple_since_hist as = Some idx \<and> idx \<le> idx_oldest)"
    have "False"
    proof (cases "Mapping.lookup tuple_since_hist as")
      case None
      then show ?thesis
        using assms(1-2)
        by (metis option.simps(4))
    next
      case (Some idx)
      then have "tuple_since_tp args as lin_data_in idx_oldest idx_mid idx"
        using assms(1)
        by (auto split: option.splits)
      moreover have "idx > idx_oldest" using Some assm by auto
      ultimately have
        "idx < idx_mid"
        "idx > idx_oldest"
        "as \<notin> snd (lin_data_in ! (idx - idx_oldest - 1))"
        unfolding tuple_since_tp_def
        by auto
      moreover have "(\<forall>(t, y)\<in>set (lin_data_in). as \<in> y)"
        using assms(2)
        unfolding tuple_since_tp_def
        by auto
      ultimately show ?thesis
        using assms(3)
        by (simp add: case_prod_beta')
    qed
  }
  then show ?thesis by auto
qed

lemma idx_append: "i < length xs \<Longrightarrow> ((xs @ [x])!i) = (xs!i)"
  by (simp add: nth_append)

lemma valid_update_mmtaux'_unfolded:
  assumes valid_before: "valid_mmtaux args cur
    (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes nt_mono: "nt \<ge> cur"
  assumes "(idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys', tuple_since_hist'', hist_sat'', since_sat'') = update_mmtaux' args nt idx_mid idx_oldest maskL maskR data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat"
  shows
    "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
    "table (args_n args) (args_R args) (Mapping.keys tuple_since_hist'')"
    \<comment> \<open>data_prev\<close>
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as)"
    "auxlist_data_prev args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) = (linearize data_prev')"
    "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
    "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l (proj_tuple maskL as))"
    "length (linearize data_prev') + idx_mid' = idx_next"

    "auxlist_data_prev args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) = drop (length (linearize data_in'')) (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)"
    \<comment> \<open>data_in\<close>
    "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in''))). wf_tuple (args_n args) (args_R args) as)"
    "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist))) = ts_tuple_rel (set (linearize data_in''))"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)) = (linearize data_in'')"
    "auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)"
    "length (linearize data_in'') + idx_oldest' = idx_mid'"
    \<comment> \<open>tuple_since_hist\<close>
    "(\<forall>as. (case Mapping.lookup tuple_since_hist'' as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)
    )"
    "(\<forall>tuple. tuple \<in> hist_sat'' \<longleftrightarrow>
      (\<not>is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r
    ))"
    \<comment> \<open>since_sat\<close>
    "(\<forall>tuple. tuple \<in> since_sat'' \<longrightarrow>
      ((tuple \<in> hist_sat'') \<or> tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)))
    )"
    "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)) \<longrightarrow>
      tuple \<in> since_sat''
    )"
    "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
proof - 
  define shift_res where "shift_res = shift_end
      (flip_int_less_lower (args_ivl args))
      nt
      fst
      (empty_queue::(ts \<times> 'a option list set \<times> 'a option list set) queue, data_prev, tuple_in_once, tuple_in_once_keys)"
  define empty_queue' where "empty_queue' = fst shift_res"
  
  have data_prev'_def: "data_prev' = (fst o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp add: Let_def split: prod.splits) 
  
  define move where "move = (fst o snd o snd) shift_res"
  define move' where "move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move"

  have tuple_in_once'_def: "tuple_in_once' = (fst o snd o snd o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp add: Let_def split: prod.splits)

  have tuple_in_once_keys'_def: "tuple_in_once_keys' = (snd o snd o snd o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp add: Let_def split: prod.splits)

  define data_in' where "data_in' = fst (takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
  define in_drop where "in_drop = snd (takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
  have data_in''_def: "data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in'"
    using assms(3)
    unfolding shift_res_def data_in'_def data_in'_def move'_def move_def
    by (auto simp add: Let_def split: prod.splits)

  then have "data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' (dropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
    unfolding data_in'_def move'_def
    using takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
    by auto

  define drop_prev_len where "drop_prev_len = length move - length move'"

  have idx_mid'_def: "idx_mid' = idx_mid + length move"
    using assms(3)
    unfolding shift_res_def move_def drop_prev_len_def
    by (auto simp add: Let_def split: prod.splits)

  have idx_oldest'_def: "idx_oldest' = idx_oldest + length in_drop + drop_prev_len"
    unfolding shift_res_def in_drop_def drop_prev_len_def move'_def move_def
    using assms(3) takedropWhile_queue_snd[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
    by (auto simp add: Let_def split: prod.splits)

  have shift_end_res: "(empty_queue', data_prev', move, tuple_in_once', tuple_in_once_keys') = shift_end
      (flip_int_less_lower (args_ivl args))
      nt
      fst
      (empty_queue::(ts \<times> 'a option list set \<times> 'a option list set) queue, data_prev, tuple_in_once, tuple_in_once_keys)"
    using empty_queue'_def data_prev'_def move_def tuple_in_once'_def tuple_in_once_keys'_def shift_res_def
    by auto
  define fold_op_f where "fold_op_f = (\<lambda>(t::ts, l::'a option list set, r::'a option list set) (tuple_since_hist:: ('a option list, nat) mapping, hist_sat:: 'a option list set, idx_move, since_sat).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist;
          hist_sat         = hist_sat \<inter> r;
          since_sat        = since_sat \<inter> r

      in 
      (
        upd_set tuple_since_hist (\<lambda>_. idx_move) (r - Mapping.keys tuple_since_hist),
        hist_sat,
        idx_move+1, 
        since_sat \<union> proj_tuple_in_join_optim (args_pos args) r (join_mask (args_n args) (args_R args)) l (join_mask (args_n args) (args_L args))
      ) 
    )"

  obtain tuple_since_hist' x hist_sat' since_sat' where fold_tuple_res: "(tuple_since_hist', hist_sat', x, since_sat') = fold fold_op_f move (tuple_since_hist, hist_sat, idx_mid, since_sat)"
    using assms(3)
    unfolding fold_op_f_def move_def shift_res_def
    by (auto simp only: update_mmtaux'.simps Let_def fst_def snd_def o_def split: prod.splits)
  then have tuple_since_hist''_def: "tuple_since_hist'' = (if (idx_mid' = idx_oldest') then Mapping.empty else tuple_since_hist')"
    using assms(3) 
    unfolding fold_op_f_def move_def shift_res_def
    by (auto simp only: update_mmtaux'.simps Let_def fst_def snd_def o_def split: prod.splits)

  have since_sat''_def: "since_sat'' = (if (idx_mid' = idx_oldest') then {} else since_sat')"
    using assms(3) fold_tuple_res
    unfolding fold_op_f_def move_def shift_res_def
    by (auto simp only: update_mmtaux'.simps Let_def fst_def snd_def o_def split: prod.splits)

  have hist_sat''_def: "hist_sat'' = (case fst (safe_hd data_in'')
    of None \<Rightarrow>
      {} 
    | Some db \<Rightarrow>
      hist_sat' \<union> {tuple \<in> (snd db).
        case (Mapping.lookup tuple_since_hist'' tuple) of
          Some idx \<Rightarrow> idx \<le> idx_oldest'
         | None \<Rightarrow> False
      })"
    using assms(3) fold_tuple_res
    unfolding fold_op_f_def move_def shift_res_def
    by (auto simp only: update_mmtaux'.simps Let_def fst_def snd_def o_def split: prod.splits)

  from assms(1) have table_tuple_in: "table (args_n args) (args_L args) (Mapping.keys tuple_in_once)"
    by auto

  from assms(1) have time: "cur = mt" by auto

  have auxlist_tuples_lhs: "ts_tuple_rel_f (\<lambda>_. {}) (set ((auxlist_data_prev args mt) auxlist)) =
    {tas \<in> (ts_tuple_rel_f (\<lambda>_. {}) (set (linearize empty_queue))) \<union> (ts_tuple_rel_binary_lhs (set (linearize data_prev))).
    False}"
    using ts_tuple_rel_empty
    by auto

  (* ts_tuple_rel_binary_lhs (set (auxlist_data_prev args mt auxlist)) =
    {tas \<in> ts_tuple_rel_binary_lhs (set (linearize empty_queue)) \<union> ts_tuple_rel_f (\<lambda>_. {}) (set (linearize data_prev)). valid_tuple tuple_in_once tas}*)

  from assms(1) have
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    by (auto simp only: valid_mmtaux.simps)

  moreover have "sorted (map fst (linearize data_prev))"
    using data_sorted[OF assms(1)]
    by auto

  moreover have "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (args_ivl args) (cur - t))"
    using data_prev_ts_props[OF assms(1)] nt_mono time
    by auto
  ultimately have
    (*"(\<forall>as \<in> \<Union>(relL ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>(relR ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"*)
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (args_ivl args) (cur - t))"
    by auto
  then have data_prev_props:
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> memL (flip_int_less_lower (args_ivl args)) (cur - t))"
    using flip_int_less_lower_memL
    by auto
  
  have data_in_props:
    "sorted (map fst (linearize data_in))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> memL (args_ivl args) (cur - t))"
    using data_sorted[OF assms(1)] data_in_ts_props[OF assms(1)] nt_mono time
    by auto

  have empty_queue_props:
    "(\<forall>as \<in> \<Union>((fst o snd) ` (set (linearize empty_queue))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((snd o snd) ` (set (linearize empty_queue))). wf_tuple (args_n args) (args_R args) as)"
    "sorted (map fst (linearize empty_queue))"
    "(\<forall>t \<in> fst ` set (linearize empty_queue). t \<le> nt \<and> \<not> memL (flip_int_less_lower (args_ivl args)) (cur - t))"
    by (auto simp add: empty_queue_rep)

  from assms(1) have max_ts_tuple_in:
    "newest_tuple_in_mapping fst data_prev tuple_in_once (\<lambda>x. True)"
    by auto

  (*

  "ts_tuple_rel_binary_lhs (set ((auxlist_data_prev args mt) auxlist)) =
    {tas \<in> (ts_tuple_rel_binary_lhs (set (linearize data_prev))) \<union> (ts_tuple_rel_f (\<lambda>_. {}) (set (linearize data_in))).
    valid_tuple tuple_in_once tas}"

*)
  have nt_mono: "nt \<ge> cur" "nt \<le> nt" using nt_mono by auto
  have shift_end_props:
    "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
    "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
    "sorted (map fst (linearize data_prev'))"
    "\<forall>t\<in>fst ` set (linearize data_prev'). t \<le> nt \<and> mem (flip_int_less_lower (args_ivl args)) (cur - t)"
    "move = snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev)"
    "linearize data_prev' = filter (\<lambda>(t, X). memR (flip_int_less_lower (args_ivl args)) (nt - t)) (linearize data_prev)"
    "tuple_in_once' =
    fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in) move tuple_in_once"
    "tuple_in_once_keys = Mapping.keys tuple_in_once \<Longrightarrow> tuple_in_once_keys' = Mapping.keys tuple_in_once'"
    unfolding relL_def relR_def
    using valid_shift_end_unfolded [of
        "(args_n args)" "(args_L args)" tuple_in_once "(\<lambda>_. {})" "(auxlist_data_prev args mt)" auxlist
        "(\<lambda>_. {})" empty_queue fst data_prev "(\<lambda>db. False)" fst "(args_L args)"
        nt "flip_int_less_lower (args_ivl args)" cur fst "(\<lambda>x. True)" nt empty_queue' data_prev' move tuple_in_once',
        OF table_tuple_in auxlist_tuples_lhs empty_queue_props(1, 3-4) 
        data_prev_props max_ts_tuple_in nt_mono shift_end_res
      ]
    by (auto simp add: ts_tuple_rel_empty)

  show
    "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
    "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
    using shift_end_props(1,2)
    by auto

  have "tuple_in_once_keys = Mapping.keys tuple_in_once"
    using assms(1)
    by auto
  then show "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
    using shift_end_props(8)
    by auto

  from assms(1) have auxlist_prev: "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    by auto

  {
    assume "mem (args_ivl args) 0"
    then have "(linearize data_prev) = []"
      using auxlist_prev memL_mono
      unfolding auxlist_data_prev_def
      by auto
    moreover have empty: "linearize data_prev' = []"
      using shift_end_props(6) calculation(1)
      by auto
    ultimately have "(linearize data_prev) = (linearize data_prev')" "(linearize data_prev) = []"  by auto
  }
  then have data_prev_eq_mem_0: "mem (args_ivl args) 0 \<longrightarrow> (linearize data_prev) = (linearize data_prev') \<and> (linearize data_prev) = []"
    by blast

  
  have data_prev'_eq: "linearize data_prev' = filter (\<lambda>(t, X). \<not>memL (args_ivl args) (nt - t)) (linearize data_prev)"
  proof (cases "mem (args_ivl args) 0")
    case True
    then show ?thesis
      using data_prev_eq_mem_0
      by auto
  next
    case False
    then have not_mem: "\<not> memL (args_ivl args) 0" by auto
    show ?thesis
      using shift_end_props(6) flip_int_less_lower_memR[OF not_mem]
      by auto
  qed

  have move_def: "move = snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev)"
  proof (cases "mem (args_ivl args) 0")
    case True
    then show ?thesis
      using shift_end_props(5) data_prev_eq_mem_0
      by (metis takeWhile.simps(1) takedropWhile_queue_snd)
  next
    case False
    then have not_mem: "\<not> memL (args_ivl args) 0" by auto
    then show ?thesis
      using shift_end_props(5) flip_int_less_lower_memR[OF not_mem]
      by auto
  qed
  then have move_takeWhile: "move = takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)"
    using takedropWhile_queue_snd
    by auto
  then have move_filter: "move = filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)"
    using data_sorted[OF assms(1)] sorted_filter_takeWhile_memL[of "linearize data_prev" args nt]
    by auto
  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t,_). (memL (args_ivl args) (nt - t)) \<and> (memR (args_ivl args) (nt - t)))"
    by auto
  have move'_eq: "move' = filter (\<lambda>(t,_). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t)) (linearize data_prev)"
    using move'_def move_filter filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by (auto simp add: filter_simp)

  have filter_data_prev_nt: "filter (\<lambda>(t, _). \<not>memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist) = (linearize data_prev')"
    using auxlist_prev data_prev'_eq
    by auto
  then have auxlist_prev_eq: "(filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (nt - t))) auxlist) = (linearize data_prev')"
    unfolding auxlist_data_prev_def
    using filter_filter[of "(\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t))" "(\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t))" auxlist]
    by auto
  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (nt - t))) = (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t))"
    by auto
  have filter_and: "(filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t)) auxlist) = (linearize data_prev')"
    using auxlist_prev_eq
    by (simp add: filter_simp)
  moreover have not_memL_nt_mt: "\<forall>t. (\<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t)) = (\<not> memL (args_ivl args) (nt - t))"
    using nt_mono time memL_mono[of "args_ivl args"]
    by auto
  ultimately have filter_auxlist_data_prev': "filter (\<lambda>(t, X). \<not>memL (args_ivl args) (nt - t)) auxlist = (linearize data_prev')"
    by auto
  moreover have "\<forall>t. \<not>memL (args_ivl args) (nt - t) = (\<not>memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t))"
    using not_memL_imp_memR[of args]
    by auto
  ultimately have filter_eq: "filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (nt - t))) auxlist = (linearize data_prev')"
    by (smt filter_cong prod.case_eq_if)
  then show auxlist_prev_eq: "auxlist_data_prev args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = (linearize data_prev')"
    unfolding auxlist_data_prev_def
    using filter_filter[of "(\<lambda>(t, _). \<not>memL (args_ivl args) (nt - t))" "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" auxlist]
    by auto

  have filter_data_prev_nt: "filter (\<lambda>(t, rel). \<not> memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist) = auxlist_data_prev args nt auxlist"
    using filter_data_prev_nt filter_auxlist_data_prev'
    unfolding auxlist_data_prev_def
    by auto

  have "\<forall>t. \<not>memL (args_ivl args) (nt - t) = (\<not>memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t))"
    using not_memL_imp_memR[of args]
    by auto
  then have auxlist_data_prev_inv: "auxlist_data_prev args nt auxlist = auxlist_data_prev args nt (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
    unfolding auxlist_data_prev_def filter_filter
    by (simp add: filter_eq filter_auxlist_data_prev')

  {
    assume assm: "mem (args_ivl args) 0"
    then have tuple_in_once_empty: "tuple_in_once = Mapping.empty" using tuple_in_once_mem0[OF assms(1)] by auto
    have filter_simp:"(\<lambda>el tuple_in. Mapping.filter ((case el of (t, X) \<Rightarrow> \<lambda>tuple_in. filter_cond (fst X) tuple_in t) tuple_in) tuple_in) =
      (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)"
      by auto
    have "fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)
   (snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev)) Mapping.empty = Mapping.empty"
      (* Mapping.filter (filter_cond_r (fst X) (proj_tuple maskL) tuple_in t) *)
      using 
        fold_Mapping_filter_empty[of
          "\<lambda>(t, X) tuple_in. (filter_cond (fst X) tuple_in t)"
          "(snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev))"]
      by (auto simp only: filter_simp)
   
    then have "tuple_in_once' = Mapping.empty" "tuple_in_once = Mapping.empty"
      using tuple_in_once_empty shift_end_props(5) shift_end_props(7)
      by auto
  }
  then have mem0: "mem (args_ivl args) 0 \<Longrightarrow> tuple_in_once = Mapping.empty \<and> tuple_in_once' = Mapping.empty"
    by auto

  {
    assume "\<not>mem (args_ivl args) 0"
    then have False: "\<not>memL (args_ivl args) 0" by auto

    have "tuple_in_once' = fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)
        move tuple_in_once"
      using shift_end_props(7)
      by auto
    then have tuple_in_once'_eq: "tuple_in_once' = fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)
      (snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev)) tuple_in_once"
      unfolding move_def
      using flip_int_less_lower_memR[OF False]
      by auto
    define fold_fn :: "(nat \<times> 'a option list set \<times> 'a option list set) \<Rightarrow> ('a option list, nat) mapping \<Rightarrow> ('a option list, nat) mapping"
      where "fold_fn = (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond (fst X) tuple_in t) tuple_in)"
    define fold_list where "fold_list = (snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev))"
    then have tuple_in_once'_eq: "tuple_in_once' = fold fold_fn fold_list tuple_in_once"
      using tuple_in_once'_eq
      unfolding fold_fn_def fold_list_def
      by simp

    from fold_list_def have fold_list_props: "\<forall>(t, X) \<in> set fold_list. memL (args_ivl args) (nt - t)"
      using takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
      set_takeWhileD
      unfolding fold_list_def
      by fastforce

    {
      fix tuple
      assume t'_props: "Mapping.lookup tuple_in_once tuple = None"     
      then have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = None"
        using fold_Mapping_filter_None[of tuple_in_once tuple fst fold_list]
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
        using tuple_in_once'_eq t'_props
        by auto
    }
    then have none: "\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      by auto

    {
      fix t tuple
      assume t_props: "Mapping.lookup tuple_in_once tuple = Some t" "memL (args_ivl args) (nt - t)"
      from assms(1) have "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l (proj_tuple maskL as))"
        by auto
      then obtain X where X_props: "(t, X) \<in> set (linearize data_prev)" "join_cond (args_pos args) (fst X) (proj_tuple maskL tuple)"
        using t_props
        by (smt Mapping_keys_intro fst_conv option.simps(3) option.simps(5))
      moreover have
        "(\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args)"
        "auxlist_data_prev args mt auxlist = (linearize data_prev)"
        using assms(1)
        by auto
      ultimately have pos: "args_pos args"
        using memL_mono[of "args_ivl args" "0"]
        unfolding auxlist_data_prev_def
        by auto

      obtain i where i_props: "i \<in> {0..<length (linearize data_prev)}" "(linearize data_prev)!i = (t, X)"
        using X_props
        by (meson atLeastLessThan_iff leI not_less0 nth_the_index the_index_bounded)
      {
        assume assm: "(t, X) \<notin> set (takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev))"
        then have "\<exists>j. j<i \<and> \<not>((\<lambda>(t, X). memL (args_ivl args) (nt - t)) ((linearize data_prev)!j))"
        (* generated subproof *)
        proof -
          have f1: "i = length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) \<or> length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) < i"
            using assm i_props(2)
            by (metis (no_types) in_set_conv_nth linorder_neqE_nat takeWhile_nth)
          have "length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) < length (linearize data_prev)"
            using X_props(1) assm
            by (metis (no_types) length_takeWhile_less takeWhile_eq_all_conv)
          then show ?thesis
            using f1 i_props(2) t_props(2) nth_length_takeWhile
            by fastforce
        qed
        then obtain j where j_props: "j<i" "\<not>memL (args_ivl args) (nt - (fst ((linearize data_prev)!j)))"
          by fastforce
        moreover have "fst ((linearize data_prev)!j) \<le> fst ((linearize data_prev)!i)"
          using i_props(1) j_props(1) data_sorted[OF assms(1)]
          by (smt atLeastLessThan_iff le_less_trans length_map less_imp_le_nat nth_map sorted_nth_mono)
        ultimately have "\<not>memL (args_ivl args) (nt - (fst ((linearize data_prev)!i)))"
          using j_props memL_mono
          by auto
        then have "False" using i_props t_props by auto
      }
      then have "(t, X) \<in> set (takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev))"
        using t_props(2)
        by auto
      then have "(t, X) \<in> set fold_list"
        unfolding fold_list_def
        using takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
        by auto
      moreover have "tuple \<in> fst X"
      proof -
        have maskL:
          "maskL = join_mask (args_n args) (args_L args)"
          using assms(1)
          by auto
        have "wf_tuple (args_n args) (args_L args) tuple"
          by (metis Mapping_keys_intro option.simps(3) t_props(1) table_def table_tuple_in)
        then show ?thesis 
          using X_props(2) maskL wf_tuple_proj_idle[of "args_n args" "args_L args" tuple] pos
          by auto
      qed
      ultimately have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = None"
        using fold_Mapping_filter_Some_None[of tuple_in_once tuple t fst _ fold_list] t_props(1) X_props(2)
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once' tuple = None"
        using tuple_in_once'_eq
        by auto
    }
    then have Some_none:
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None"
      by auto

    {
      fix t tuple
      assume t_props: "Mapping.lookup tuple_in_once tuple = Some t" "\<not>memL (args_ivl args) (nt - t)"
      {
        fix X
        assume "(t, X) \<in> set fold_list"
        then have "memL (args_ivl args) (nt - t)"
          using fold_list_props
          by auto
        then have "False" using t_props by auto
      }
      then have "(\<And>X. (t, X) \<in> set fold_list \<Longrightarrow> tuple \<notin> fst X)" by auto
      moreover have "Mapping.lookup tuple_in_once tuple = Some t" using t_props by auto
      ultimately have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = Mapping.lookup tuple_in_once tuple"
        using fold_Mapping_filter_Some_Some[of tuple_in_once tuple t fold_list fst]
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
        using tuple_in_once'_eq
        by auto
    }
    then have tuple_in_once_eq_Some:
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None"
      "\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      using none Some_none
      by auto
  }
  then have
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t  \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    by auto

  moreover {
    assume "mem (args_ivl args) 0"
    then have "\<forall>tuple. Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      using mem0
      by auto
  }
  ultimately have tuple_in_once_lookup:
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t  \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    by auto

  have tuple_in_once'_subseteq: "Mapping.keys tuple_in_once' \<subseteq> Mapping.keys tuple_in_once"
  proof (cases "mem (args_ivl args) 0")
  case True
    then show ?thesis using mem0 by blast
  next
    case False
    {
      fix k
      assume "k \<in> Mapping.keys tuple_in_once'"
      then have "k \<in> Mapping.keys tuple_in_once"
        using False tuple_in_once_lookup(3)
        by (metis domIff keys_dom_lookup)
    }
    then show ?thesis by auto
  qed

  from assms(1) have data_prev_wf:
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    by auto

  then show
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as)"
    using shift_end_props(6)
    by auto

  from assms(1) have tuple_in_once_props:
    "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> join_cond (args_pos args) l (proj_tuple maskL as))"
    by auto
  {
    fix as t
    assume assm: "Mapping.lookup tuple_in_once' as = Some t"
    then have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l (proj_tuple maskL as)"
    proof (cases "mem (args_ivl args) 0")
      case True
      then show ?thesis
        using assm mem0
        by (simp add: Mapping.lookup_empty)
    next
      case False
      from assm have "as \<in> Mapping.keys tuple_in_once'"
        by (simp add: Mapping_keys_intro)
      then have as_mem: "as \<in> Mapping.keys tuple_in_once"
        using assm tuple_in_once'_subseteq
        by auto
      then obtain t' where t'_props: "Mapping.lookup tuple_in_once as = Some t'"
        using Mapping_keys_dest[of as tuple_in_once]
        by auto
      show ?thesis
      proof (cases "memL (args_ivl args) (nt - t')")
        case True
        then have "Mapping.lookup tuple_in_once' as = None"
          using False t'_props tuple_in_once_lookup(2)
          by auto
        then show ?thesis using assm by auto
      next
        case not_memL: False
        then have "Mapping.lookup tuple_in_once' as = Some t'"
          using False t'_props tuple_in_once_lookup(1)
          by auto
        then have t_eq: "t=t'" "Mapping.lookup tuple_in_once as = Some t"
          using assm t'_props
          by auto
        then obtain l r where tlr_props: "(t, l, r) \<in> set (linearize data_prev)" "(join_cond (args_pos args) l (proj_tuple maskL as))"
          using as_mem tuple_in_once_props
          by fastforce
        then have "(t, l, r) \<in> set (linearize data_prev')"
          using False not_memL data_prev'_eq t_eq(1)
          by auto
        then show ?thesis
          using tlr_props
          by auto
      qed
    qed
  }
  then show "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l (proj_tuple maskL as))"
    using Mapping_keys_dest
    by fastforce

  have filter_simp: "(\<lambda>(t, _). mem (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, _) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t)))" by auto
  have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    unfolding drop_prev_len_def move_filter move'_eq
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_prev))"
    by (auto simp add: filter_simp)
  then have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by auto
  moreover have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) =
    length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) +
    length (filter (\<lambda>x. \<not> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t))) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)"]
    by auto
  ultimately have "drop_prev_len = length (filter (\<lambda>x. \<not> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t))) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    by (simp add: case_prod_beta')
  then have "drop_prev_len = length (filter (\<lambda>x. (case x of (t, _) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> \<not> memR (args_ivl args) (nt - t))) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by (simp add: case_prod_beta')
  moreover have "\<forall>t. (memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) = (\<not> memR (args_ivl args) (nt - t))"
    using not_memR_imp_memL[of args]
    by auto
  ultimately have drop_prev_len_eq: "drop_prev_len = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto

  from assms(1) have data_prev_len: "length (linearize data_prev) + idx_mid = idx_next" by auto

  have "length (linearize data_prev') = length (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using data_prev'_eq
    by auto
  then have lin_prev'_len: "length (linearize data_prev') = length (filter (\<lambda>x. \<not> (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t))) (linearize data_prev))"
    by (metis (mono_tags, lifting) case_prod_beta' filter_cong)
  
  have idx_mid'_eq: "idx_mid' = idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using idx_mid'_def move_filter
    by blast

  then have "idx_mid' - idx_mid = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto

  then have "length (linearize data_prev') + (idx_mid' - idx_mid) = length (linearize data_prev)"
    using lin_prev'_len sum_length_filter_compl[of "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  
  then show "length (linearize data_prev') + idx_mid' = idx_next"
    using data_prev_len
    by (auto simp add: idx_mid'_def)

  from assms(1) have data_in_len: "length (linearize data_in) + idx_oldest = idx_mid" by auto
  then have mid_geq_old: "idx_mid \<ge> idx_oldest" by auto

  have idx_oldest'_eq: "idx_oldest' = idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len"
    using idx_oldest'_def
    unfolding in_drop_def
    using takedropWhile_queue_snd[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
      data_sorted[OF assms(1)] sorted_filter_takeWhile_not_memR[of "linearize data_in" args nt]
    by auto
  then have "idx_mid' + idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len = idx_oldest' + idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using idx_mid'_eq
    by auto
  then have len_eq: "idx_mid' + idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len = idx_oldest' + idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  have "(\<forall>x. (\<not> memR (args_ivl args) (fst x)) \<longrightarrow> (memL (args_ivl args) (fst x)))"
    using not_memR_imp_memL[of args]
    by auto
  then have prev_not_memR_leq_prev_memL: "length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) \<le> length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_imp[of "\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)" "\<lambda>(t, _). memL (args_ivl args) (nt - t)" "linearize data_prev"]
    by auto
  have "idx_oldest' \<le> idx_mid + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    unfolding idx_oldest'_eq drop_prev_len_eq
    using data_in_len
    by auto
  then have mid'_geq_old': "idx_oldest' \<le> idx_mid'"
    unfolding idx_mid'_eq
    using prev_not_memR_leq_prev_memL
    by auto

  have "linearize data_in'' = linearize data_in' @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move)"
    using data_in''_def fold_append_queue_map[of move' data_in'] move'_def
    by auto
  then have "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using data_in'_def takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
          data_sorted[OF assms(1)]
          dropWhile_queue_rep[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
          sorted_filter_dropWhile_memR[of "linearize data_in" args nt] move_def
          takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
          sorted_filter_takeWhile_memL[of "linearize data_prev" args nt]
    by auto
  moreover have "filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_prev) = filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)"
    by (simp add: case_prod_beta')
  ultimately have lin_data_in''_eq: "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  then have "length (linearize data_in'') = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  then have "length (linearize data_in'') + length (filter (\<lambda>x. \<not> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(linearize data_in)"]
    by auto
  then have data_in''_len: "length (linearize data_in'') + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by (auto simp add: case_prod_beta')

  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t))"
    by auto

  have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)"]
          filter_filter[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by (auto simp add: case_prod_beta')
  moreover have "\<forall>t. (memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) = (\<not> memR (args_ivl args) (nt - t))"
    using not_memR_imp_memL[of args]
    by auto
  ultimately have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  then have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t)) (linearize data_prev)) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by (auto simp add: filter_simp)
  then have len_simp: "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  have "idx_mid' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + idx_oldest' + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using len_eq idx_mid'_eq data_in_len drop_prev_len_eq
    by auto
  then have "idx_mid' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + idx_oldest' + (length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)))"
    using prev_not_memR_leq_prev_memL
    by auto
  then have "idx_mid' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + idx_oldest' + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by (auto simp only: len_simp)
  then show data_in''_len': "length (linearize data_in'') + idx_oldest' = idx_mid'"
    using data_in''_len
    by auto
  then have tuple_since_hist''_def: "tuple_since_hist'' = (if (is_empty data_in'') then Mapping.empty else tuple_since_hist')"
    using tuple_since_hist''_def is_empty_alt[of data_in'']
    by auto

  from assms(1) have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in))). wf_tuple (args_n args) (args_R args) as)"
    by auto
  moreover have "(\<forall>as \<in> \<Union>((snd) ` (set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))))). wf_tuple (args_n args) (args_R args) as)"
    using data_prev_wf(2)
    unfolding relR_def
    by auto
  ultimately show "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in''))). wf_tuple (args_n args) (args_R args) as)"
    unfolding lin_data_in''_eq
    by auto

  have filter_simp: "(\<lambda>x. (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> mem (args_ivl args) (nt - t))) = (\<lambda>(t, _, _). mem (args_ivl args) (nt - t))"
    by auto
  have data_in_auxlist_filter_eq: "auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) = auxlist_data_in args nt auxlist"
    unfolding auxlist_data_in_def filter_filter
    by (simp add: filter_simp)

  {
    fix timed_tuple
    assume assm: "timed_tuple \<in> ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist))"
    define t where "t = fst timed_tuple"
    define tuple where "tuple = snd timed_tuple"
    from assm obtain l r where l_r_def: "tuple \<in> r" "(t, l, r) \<in> set (filter (\<lambda>(t, _, _). mem (args_ivl args) (nt - t)) auxlist)"
      unfolding ts_tuple_rel_f_def t_def tuple_def auxlist_data_in_def
      by auto
    then have mem: "mem (args_ivl args) (nt - t)" "(t, l, r) \<in> set auxlist" by auto
    then have "timed_tuple \<in> ts_tuple_rel (set (linearize data_in''))"
    proof (cases "memL (args_ivl args) (mt - t)")
      case True
      then have "(t, r) \<in> set (linearize data_in)"
        using mem(2) auxlist_mem_or[OF assms(1), of "(t, l, r)"]
        unfolding time_def
        by auto
      then have "(t, r) \<in> set (linearize data_in'')"
        unfolding lin_data_in''_eq
        using mem(1)
        by auto
      then show ?thesis
        using l_r_def(1)
        unfolding ts_tuple_rel_f_def t_def tuple_def
        by fastforce
    next
      case False
      then have "(t, l, r) \<in> set (linearize data_prev)"
        using mem(2) auxlist_mem_or[OF assms(1), of "(t, l, r)"]
        unfolding time_def
        by auto
      then have "(t, l, r) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
        using mem(1)
        by auto
      then have "(t, r) \<in> set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)))"
        by force
      then have "(t, r) \<in> set (linearize data_in'')"
        unfolding lin_data_in''_eq
        by auto
      then show ?thesis
        using l_r_def(1)
        unfolding ts_tuple_rel_f_def t_def tuple_def
        by fastforce
    qed
  }
  moreover {
    fix timed_tuple
    assume assm: "timed_tuple \<in> ts_tuple_rel (set (linearize data_in''))"
    define t where "t = fst timed_tuple"
    define tuple where "tuple = snd timed_tuple"

    from assm obtain r where tuple_props: "tuple \<in> r" "(t, r) \<in> (set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @
                  map (\<lambda>(t, l, y). (t, y)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))))"
      unfolding ts_tuple_rel_f_def lin_data_in''_eq t_def tuple_def
      by force
    then have "(t, r) \<in> (set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))) \<or> (t, r) \<in> set (map (\<lambda>(t, l, y). (t, y)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)))"
      by auto
    moreover {
      assume "(t, r) \<in> (set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)))"
      then have memR: "memR (args_ivl args) (nt - t)" "(t, r) \<in> set (linearize data_in)"
        by auto
      then have "memL (args_ivl args) (mt - t)" using data_in_mem[OF assms(1), of "(t, r)"] by auto
      then have "memL (args_ivl args) (nt - t)" using memL_mono nt_mono time by auto
      then have mem: "mem (args_ivl args) (nt - t)" using memR by auto
      have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
        using assms(1) by auto
      then have "(t, r) \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
        using memR(2)
        by auto
      then obtain l where "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
        using memR(2)
        by auto
      then have "(t, l, r) \<in> set auxlist"
        unfolding auxlist_data_in_def
        by auto
      then have "(t, l, r) \<in> set (auxlist_data_in args nt auxlist)"
        unfolding auxlist_data_in_def
        using mem
        by auto
      then have "timed_tuple \<in> ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist))"
        unfolding ts_tuple_rel_f_def auxlist_data_in_def
        using tuple_props(1) t_def tuple_def
        by fastforce
    }
    moreover {
      assume "(t, r) \<in> set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)))"
      then obtain l where "(t, l, r) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
        by auto
      then have mem: "mem (args_ivl args) (nt - t)" "(t, l, r) \<in> set (linearize data_prev)" by auto
      moreover have "auxlist_data_prev args mt auxlist = (linearize data_prev)" using assms(1) by auto
      ultimately have "(t, l, r) \<in> set (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)"
        unfolding auxlist_data_prev_def
        by auto
      then have "(t, l, r) \<in> set auxlist" by auto
      then have "(t, l, r) \<in> set (auxlist_data_in args nt auxlist)"
        unfolding auxlist_data_in_def
        using mem
        by auto
      then have "timed_tuple \<in> ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist))"
        unfolding ts_tuple_rel_f_def auxlist_data_in_def
        using tuple_props(1) t_def tuple_def
        by fastforce
    }
    ultimately have "timed_tuple \<in> ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist))"
      by blast
  }
  ultimately have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist)) = ts_tuple_rel (set (linearize data_in''))"
    by blast
  then show "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist))) = ts_tuple_rel (set (linearize data_in''))"
    using data_in_auxlist_filter_eq
    by auto

  have filter_simp: "(\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> mem (args_ivl args) (nt - t)))"
    by auto
  have filter_simp': "((\<lambda>(t, _). memR (args_ivl args) (nt - t)) \<circ> (\<lambda>(t, l, r). (t, r))) = (\<lambda>(t, _). memR (args_ivl args) (nt - t))"
    by auto
  have filter_simp'': "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). mem (args_ivl args) (mt - t) \<and> memR (args_ivl args) (nt - t))"
    by auto

  from assms(1) have auxlist_eqs:
    "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
    "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
    by auto
  then have auxlist_concat: "filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist @ filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist = auxlist"
    unfolding auxlist_data_prev_def auxlist_data_in_def
    by auto

  have "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using lin_data_in''_eq
    by auto
  moreover have in_eqs:
      "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
      "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    using assms(1)
    by auto
  ultimately have "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist)) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist))"
    unfolding auxlist_data_in_def auxlist_data_prev_def
    by auto
  then have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist)) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist))"
    using filter_map[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, l, r). (t, r))" "(filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist)"]
    by (auto simp add: filter_simp')
  then have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) ((filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist)) @ (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    by auto
  then have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) ((filter (\<lambda>(t, _). mem (args_ivl args) (mt - t) \<and> memR (args_ivl args) (nt - t)) auxlist) @ (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). mem (args_ivl args) (mt - t))" auxlist]
    by (auto simp add: filter_simp'')
  then have x: "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) ((filter (\<lambda>(t, _). mem (args_ivl args) (mt - t) \<and> mem (args_ivl args) (nt - t)) auxlist) @ (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    using mem_mt_and_memR_imp_mem[of mt nt args] nt_mono time
    by auto
  moreover have filter_simp': "(\<lambda>(t, _). mem (args_ivl args) (mt - t) \<and> mem (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (nt - t)))"
    by auto
  ultimately have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) ((filter (\<lambda>x. (case x of (t, _) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, _) \<Rightarrow> mem (args_ivl args) (nt - t))) auxlist) @ (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    by (simp only: filter_simp')
  moreover have filter_simp': "filter (\<lambda>x. (case x of (t, _) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, _) \<Rightarrow> mem (args_ivl args) (nt - t))) auxlist = filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist)"
    using filter_filter[of "(\<lambda>(t, _). mem (args_ivl args) (nt - t))" "(\<lambda>(t, _). mem (args_ivl args) (mt - t))" auxlist]
    by auto
  ultimately have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist) @ filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist))"
    unfolding filter_simp'
    by auto
  then have "linearize data_in'' = map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) ((filter (\<lambda>(t, _). mem (args_ivl args) (mt - t)) auxlist) @ (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t)) auxlist)))"
    by auto
  then have "map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) auxlist) = linearize data_in''"
    using auxlist_concat
    by auto
  moreover have "\<forall>t. (memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) = (mem (args_ivl args) (nt - t))"
    by blast
  ultimately have "map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) auxlist) = linearize data_in''"
    by auto
  then have lin_data_in''_eq: "map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) = linearize data_in''"
    using filter_filter[of "(\<lambda>(t, _). mem (args_ivl args) (nt - t))" "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" auxlist]
    by (auto simp add: filter_simp)
  then show auxlist_data_in: "map (\<lambda>(t, l, r). (t, r)) (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) = linearize data_in''"
    unfolding auxlist_data_in_def
    by auto

  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (nt - t))) = (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t))"
    by auto
  have filter_simp': "(\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) = (\<lambda>(t, _). mem (args_ivl args) (nt - t))"
    by auto


  from assms(1) have "auxlist_data_prev args mt auxlist = (linearize data_prev)"
                     "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
    by auto
  then have prev_drop_eq: "(linearize data_prev) = drop (length (linearize data_in)) auxlist" by auto

  have "length (linearize data_in'') + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using data_in''_len
    by auto
  then have "length (linearize data_in'') = length (linearize data_in) - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto

  
  have memR: "\<forall>db \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist). memR (args_ivl args) (nt - time db)"
    unfolding time_def
    by auto
  have "sorted (map fst auxlist)" using assms(1) by auto
  then have sorted: "sorted (map fst (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist))"
    using sorted_filter
    by blast
  have "length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) = length (linearize data_in'')"
    using lin_data_in''_eq
    by (smt length_map)

  then have filter_take_eq: "filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using take_filter_mem[OF memR sorted]
    by auto
  then show auxlist_data_in_take_eq: "auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    unfolding auxlist_data_in_def
    by auto

  from filter_take_eq have "(filter (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> mem (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using filter_filter[of "(\<lambda>(t, _). mem (args_ivl args) (nt - t))" "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" auxlist]
    by (auto simp add: filter_simp)
  then have filter_auxlist_take: "(filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    by (simp only: filter_simp')

  have filter_simp: "(\<lambda>(t, _). mem (args_ivl args) (nt - t)) = (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> memL (args_ivl args) (nt - t))"
    by auto
  have filter_simp': "(\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> memL (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)))"
    by auto
  have filter_simp'': "(\<lambda>x. \<not> (case x of (t, _) \<Rightarrow> memL (args_ivl args) (nt - t))) = (\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t))"
    by auto

  have "(filter (\<lambda>(t, _). memR (args_ivl args) (nt - t) \<and> memL (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using filter_auxlist_take
    by (auto simp add: filter_simp)
  then have "filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = take (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using filter_filter[of "(\<lambda>(t, _). mem (args_ivl args) (nt - t))" "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" auxlist]
    by (auto simp add: filter_simp')
  then have "filter (\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) = drop (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    using filter_take_drop[of "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)" "(length (linearize data_in''))"]
    by (simp only: filter_simp'')
  then show "auxlist_data_prev args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist) =
    drop (length (linearize data_in'')) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)"
    unfolding auxlist_data_prev_def
    by auto

  {
    fix as

    define idx_oldest_mv where "idx_oldest_mv = (\<lambda>move::(ts \<times> 'a option list set \<times> 'a option list set) list.
      idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + length move - length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move)
    )"
    define idx_mid_mv where "idx_mid_mv = (\<lambda>move::(ts \<times> 'a option list set \<times> 'a option list set) list.
      idx_mid + length move
    )"
    define lin_data_in''_mv where "lin_data_in''_mv = (\<lambda>move::(ts \<times> 'a option list set \<times> 'a option list set) list.
      linearize data_in' @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move)
    )"

    have filter_simp: "(\<lambda>x. \<not> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))"
      by auto

    have data_in'_eq: "linearize data_in' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)"
      unfolding data_in'_def
      using takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
            dropWhile_queue_rep[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
            data_sorted[OF assms(1)] sorted_filter_dropWhile_memR[of "linearize data_in" args nt]
      by auto

    {
      fix move::"(ts \<times> 'a option list set \<times> 'a option list set) list"
      have "length ((linearize data_in)) + idx_oldest = idx_mid"
        using data_in_len
        by blast
      then have "length (lin_data_in''_mv move) + idx_oldest_mv move = idx_mid_mv move"
        unfolding lin_data_in''_mv_def idx_oldest_mv_def idx_mid_mv_def
        unfolding data_in'_eq
        using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "move"]
              sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "linearize data_in"]
        by (auto simp add: filter_simp)
    }
    then have mv_ln_eq: "\<forall>move. length (lin_data_in''_mv move) + idx_oldest_mv move = idx_mid_mv move" 
      by auto

    define tuple_since_hist_mv where "tuple_since_hist_mv = (\<lambda>(move::(ts \<times> 'a option list set \<times> 'a option list set) list) tuple.
      if ((idx_mid_mv move) = (idx_oldest_mv move)) then
        Mapping.empty
      else
        fst (fold fold_op_f move tuple)
    )"
   
    define hist_sat_mv where "hist_sat_mv = (\<lambda>move tuple.
      (case (lin_data_in''_mv move)
        of [] \<Rightarrow>
          {} 
        | (db#dbs) \<Rightarrow>
          ((fst o snd) (fold fold_op_f move tuple)) \<union> {as \<in> (snd db).
            case (Mapping.lookup (tuple_since_hist_mv move tuple) as) of
              Some idx \<Rightarrow> idx \<le> (idx_oldest_mv move)
            | None \<Rightarrow> False
          })
    )"

    define since_sat_mv where "since_sat_mv = (\<lambda>move tuple.
      if ((idx_mid_mv move) = (idx_oldest_mv move)) then
        {}
      else
        (snd o snd o snd) (fold fold_op_f move tuple)
    )"

    define data_in'_aux where "data_in'_aux =
      filter (\<lambda>(t, _). memR (args_ivl args) (nt - t))(take (length (linearize data_in)) auxlist)
    "

    have filter_map_simp: "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) = filter ((\<lambda>(t, _). memR (args_ivl args) (nt - t)) \<circ> (\<lambda>(t, l, r). (t, r)))"
      by (metis (mono_tags, lifting) case_prod_beta' fst_conv o_apply)

    (* check if defined correctly *)
    have data_in'_aux_eq: "map (\<lambda>(t, l, r). (t, r)) data_in'_aux = linearize data_in'"
      using in_eqs(1) auxlist_eqs(2)
      unfolding data_in'_aux_def data_in'_eq
      using filter_map[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, l, r). (t, r))" "(take (length (linearize data_in)) auxlist)"]
      by (auto simp add: filter_map_simp)

    define lin_data_in''_aux_mv where "lin_data_in''_aux_mv = (\<lambda>move::(ts \<times> 'a option list set \<times> 'a option list set) list.
      data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move
    )"

    have data_in''_aux_eq: "\<forall>move. map (\<lambda>(t, l, r). (t, r)) (lin_data_in''_aux_mv move) = lin_data_in''_mv move"
      using data_in'_aux_eq
      unfolding lin_data_in''_aux_mv_def lin_data_in''_mv_def
      by auto

    define init_tuple where "init_tuple = (tuple_since_hist, hist_sat, idx_mid, since_sat)"

    define get_idx_move::"(('a option list, nat) mapping \<times> 'a option list set \<times> nat \<times> 'a option list set) \<Rightarrow> nat"
      where "get_idx_move = fst o snd o snd"

    from assms(1) have tuple_init_props: "(\<forall>as. (case Mapping.lookup tuple_since_hist as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx)
    )"
      by auto (* map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)*)


    from assms(1) have in_eq: "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
      by auto
    {
      fix P
      have "(\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). P r) = (\<forall>(t, r) \<in> set (linearize data_in). P r)"
      proof (rule iffI)
        assume "(\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). P r)"
        then have "\<forall>(t, r)\<in>set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)). P r"
          by auto
        then show "(\<forall>(t, r) \<in> set (linearize data_in). P r)" using in_eq by auto
      next
        assume "\<forall>(t, r)\<in>set (linearize data_in). P r"
        then have "\<forall>(t, r)\<in>set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)). P r"
          using in_eq
          by auto
        then show "\<forall>(t, l, r)\<in>set (auxlist_data_in args mt auxlist). P r" by auto
      qed
    }
    then have "\<forall>P. (\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). P r) = (\<forall>(t, r) \<in> set (linearize data_in). P r)"
      by auto
    moreover from assms(1) have "(\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
        (\<not>is_empty data_in) \<and> (
          \<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r
      ))"
      by auto
    ultimately have tuple_init_props_hist_sat: "(\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
      (\<not>is_empty data_in) \<and> (
        \<forall>(t, r) \<in> set (linearize data_in). tuple \<in> r
    ))" by auto

    have tuple_init_props_since:
      "(\<forall>tuple. tuple \<in> since_sat \<longrightarrow>
        ((tuple \<in> hist_sat) \<or> tuple_since_lhs tuple (linearize data_in) args maskL (auxlist_data_in args mt auxlist))
      )"
      "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in) args maskL (auxlist_data_in args mt auxlist) \<longrightarrow>
        tuple \<in> since_sat
      )"
      using assms(1)
      unfolding valid_mmtaux.simps
      apply -
      apply (erule conjE)+
       apply assumption
      apply -
      apply (erule conjE)+
       apply assumption
      done

    
    have mv_data_in'': "linearize data_in'' = lin_data_in''_mv move"
      using data_in''_def fold_append_queue_map[of move' data_in'] move'_def
      unfolding lin_data_in''_mv_def
      by auto
    moreover have mv_idx_oldest': "idx_oldest' = idx_oldest_mv move"
      using idx_oldest'_eq
      unfolding idx_oldest_mv_def drop_prev_len_def move'_def
      by auto
    moreover have mv_idx_mid': "idx_mid' = idx_mid_mv move"
      unfolding idx_mid_mv_def idx_mid'_def init_tuple_def
      by auto
    ultimately have "length (lin_data_in''_mv move) + (idx_oldest_mv move) = (idx_mid_mv move)"
      using data_in''_len'
      by auto
    moreover have "sorted (map fst move)" "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t < t'"
      unfolding move_filter
      using data_sorted[OF assms(1)]
       apply (auto simp add: sorted_filter)
      by fastforce
    moreover have "\<forall>(t, l, r) \<in> set move. table (args_n args) (args_L args) l \<and> table (args_n args) (args_R args) r"
    proof -
      have
        "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as)"
        "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
        using assms(1)
        by auto
      then show ?thesis
        unfolding move_filter table_def relL_def relR_def
        by auto
    qed
    ultimately have "
    \<comment> \<open>historically\<close>
    (case Mapping.lookup (tuple_since_hist_mv move init_tuple) as of
      Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv move) (idx_oldest_mv move) (idx_mid_mv move) idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv move) (idx_oldest_mv move) (idx_mid_mv move) idx) \<and>
    (as \<in> (hist_sat_mv move init_tuple) \<longleftrightarrow>
      ((lin_data_in''_mv move) \<noteq> []) \<and> (
        \<forall>(t, r) \<in> set (lin_data_in''_mv move). as \<in> r
    )) \<and>
     \<comment> \<open>since\<close>
    (as \<in> (since_sat_mv move init_tuple) \<longrightarrow>        
      ((as \<in> (hist_sat_mv move init_tuple)) \<or> tuple_since_lhs as (lin_data_in''_mv move) args maskL (lin_data_in''_aux_mv move))
    ) \<and>
    (tuple_since_lhs as (lin_data_in''_mv move) args maskL (lin_data_in''_aux_mv move) \<longrightarrow>
      as \<in> (since_sat_mv move init_tuple)
    ) \<and>
    \<comment> \<open>other required properties\<close>
    get_idx_move (fold fold_op_f move init_tuple) = (idx_mid_mv move) \<and>
    (case Mapping.lookup (fst (fold fold_op_f move init_tuple)) as of Some idx \<Rightarrow> idx < (idx_mid_mv move) | None \<Rightarrow> True)"
    proof (induction move rule: rev_induct)
      case Nil
      then have lin_data_in''_eq: "lin_data_in''_mv [] = drop (length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))) (linearize data_in)"
        unfolding lin_data_in''_mv_def data_in'_def
        using takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
              dropWhile_queue_rep[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
              data_sorted[OF assms(1)] sorted_filter_dropWhile_memR[of "linearize data_in" args nt]
              drop_filter_memR[of "linearize data_in" "(args_ivl args)" nt ]
        by auto
      have idx_oldest'_eq: "idx_oldest_mv [] = idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
        unfolding idx_oldest_mv_def
        using Nil
        by auto

      have idx_mid'_eq: "idx_mid_mv [] = idx_mid"
        unfolding idx_mid_mv_def
        using Nil
        by (simp add: case_prod_beta')
      
      have tuple_since_hist'_eq: "fst (fold fold_op_f [] init_tuple) = fst init_tuple"
        using Nil
        by auto
      then have "case Mapping.lookup (tuple_since_hist_mv [] init_tuple) as of
        Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx
        | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx"
      proof (cases "(idx_mid_mv []) = (idx_oldest_mv [])")
        case True
        then have "tuple_since_hist_mv [] init_tuple = Mapping.empty"
          using True
          unfolding tuple_since_hist_mv_def
          by auto
        then have "Mapping.lookup (tuple_since_hist_mv [] init_tuple) as = None"
          by (simp add: Mapping.empty_def Mapping.lookup.abs_eq)
        moreover have "\<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx"
          using True Nil
          unfolding tuple_since_tp_def 
          by auto
        ultimately show ?thesis by auto
      next
        define idx_move where "idx_move = get_idx_move init_tuple"
        case non_empty: False
        have "case Mapping.lookup (fst (fold fold_op_f [] init_tuple)) as of
            None     \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx
          | Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx
        "
        proof (cases "Mapping.lookup (fst (fold fold_op_f [] init_tuple)) as")
          case None
          then have tuple_since_tp: "\<forall>idx. \<not>tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
            using tuple_since_hist'_eq Nil idx_mid'_eq tuple_init_props
            unfolding idx_move_def get_idx_move_def init_tuple_def
            by (auto simp add: option.case_eq_if)
          then have idx_props: "\<forall>idx<idx_mid. (
              linearize data_in = [] \<or>
              \<not>(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
                as \<in> r
              ) \<or>
              \<not>(idx > idx_oldest \<longrightarrow> as \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))
            )"
            unfolding tuple_since_tp_def
            by blast
          {
            assume assm: "(linearize data_in) \<noteq> []"
            then have idx_props: "\<forall>idx<idx_mid. (
              \<not>(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
                as \<in> r
              ) \<or>
              \<not>(idx > idx_oldest \<longrightarrow> as \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))
            )"
              using idx_props
              by blast

            then have "as \<notin> snd (last (linearize data_in))"
              using no_hist_last_not_sat[OF data_in_len tuple_since_tp assm]
              by auto
          }
          then have "(linearize data_in) \<noteq> [] \<longrightarrow> as \<notin> snd (last (linearize data_in))"
            by auto
          moreover have "(lin_data_in''_mv []) \<noteq> [] \<longrightarrow> (linearize data_in) \<noteq> [] \<and> (last (linearize data_in) = last (lin_data_in''_mv []))"
            using lin_data_in''_eq
            by auto
          ultimately have last_props: "lin_data_in''_mv [] \<noteq> [] \<longrightarrow> as \<notin> snd (last (lin_data_in''_mv []))"
            by auto
          {
            fix idx
            assume assm: "lin_data_in''_mv [] \<noteq> []" "idx < (idx_mid_mv [])" "(idx > (idx_oldest_mv []) \<longrightarrow> as \<notin> (snd ((lin_data_in''_mv [])!(idx-(idx_oldest_mv [])-1))))"
            then have "idx - (idx_oldest_mv []) < length (lin_data_in''_mv [])"
              using Nil
              by (metis diff_is_0_eq leI length_greater_0_conv less_diff_conv2 nat_less_le)
            then have "last (lin_data_in''_mv []) \<in> set (drop (idx-(idx_oldest_mv [])) (lin_data_in''_mv []))"
              by (metis drop_eq_Nil last_drop last_in_set leD)
            moreover have "as \<notin> snd (last (lin_data_in''_mv []))"
              using assm(1) last_props
              by auto
            ultimately have "\<exists>db \<in> set (drop (idx-(idx_oldest_mv [])) (lin_data_in''_mv [])). as \<notin> snd db"
              by auto
          }
          then have "\<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx"
            unfolding tuple_since_tp_def
            by (auto simp add: case_prod_beta')
          then show ?thesis using None by auto
        next
          case (Some idx)
          then have "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
            using tuple_since_hist'_eq Nil idx_mid'_eq tuple_init_props
            unfolding init_tuple_def
            apply (auto simp add: option.case_eq_if)
            by (metis option.sel option.simps(3))
          then have idx_props: "(linearize data_in) \<noteq> []" "idx < idx_mid"
              "(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
                as \<in> r
              )"
              "(idx > idx_oldest \<longrightarrow> as \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))"
            unfolding tuple_since_tp_def
            by auto
          then have idx_mid: "idx < (idx_mid_mv [])" using idx_mid'_eq by auto
          {
            define r where "r = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
            assume "\<exists>db \<in> set (drop (idx-(idx_oldest_mv [])) (lin_data_in''_mv [])). as \<notin> snd db"
            then obtain db where db_props: "db \<in> set (drop (idx - idx_oldest - r) (drop r (linearize data_in)))" "as \<notin> snd db"
              using idx_oldest'_eq lin_data_in''_eq
              unfolding r_def
              by auto
            then have  "db \<in> set (drop (idx - idx_oldest) (linearize data_in))"
              by (metis drop_list_shift in_set_dropD leI less_imp_le_nat)
            then have "False" using idx_props(3) db_props(2) by auto
          }
          then have "\<forall>(t, r) \<in> set (drop (idx-(idx_oldest_mv [])) (lin_data_in''_mv [])). as \<in> r"
            by fastforce
          moreover {
            define r where "r = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
            assume "idx > idx_oldest_mv []"
            then have idx_g: "idx > idx_oldest + r"
              using idx_oldest'_eq
              unfolding r_def
              by auto
            then have "(lin_data_in''_mv [])!(idx-(idx_oldest_mv [])-1) = linearize data_in!(idx-idx_oldest -1)"
              using idx_oldest'_eq lin_data_in''_eq
              unfolding r_def
              by (auto simp add: add.commute)
            moreover have "as \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1)))"
              using idx_props(4) idx_g
              by auto
            ultimately have "as \<notin> (snd ((lin_data_in''_mv [])!(idx-(idx_oldest_mv [])-1)))" by auto
          }
          ultimately have "tuple_since_tp args as (lin_data_in''_mv []) (idx_oldest_mv []) (idx_mid_mv []) idx"
            using idx_mid non_empty Nil
            unfolding tuple_since_tp_def
            by auto
          then show ?thesis using Some by auto
        qed
        moreover have "tuple_since_hist_mv [] init_tuple = fst (fold fold_op_f [] init_tuple)"
          using non_empty
          unfolding tuple_since_hist_mv_def
          by auto
        ultimately show ?thesis by auto
      qed
      moreover have hist_sat_props: "(as \<in> (hist_sat_mv [] init_tuple) \<longleftrightarrow>
        ((lin_data_in''_mv []) \<noteq> []) \<and> (
          \<forall>(t, r) \<in> set (lin_data_in''_mv []). as \<in> r
        ))"
      proof -
        {
          assume assm: "as \<in> (hist_sat_mv [] init_tuple)"
          then have non_empty: "lin_data_in''_mv [] \<noteq> []"
            unfolding hist_sat_mv_def
            by auto
          then obtain db dbs where db_props: "lin_data_in''_mv [] = db # dbs"
            using list.exhaust
            by blast
          have "\<forall>(t, r) \<in> set (lin_data_in''_mv []). as \<in> r"
          proof -
            {
              fix t r
              assume "(t, r) \<in> set (lin_data_in''_mv [])"
              then have list_mem: "(t, r) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))"
                unfolding lin_data_in''_mv_def data_in'_eq
                by auto
              have "(fst \<circ> snd) (fold fold_op_f [] init_tuple) = hist_sat"
                unfolding init_tuple_def 
                by auto
              moreover have "tuple_since_hist_mv [] init_tuple = tuple_since_hist"
                using non_empty Nil(1)
                unfolding tuple_since_hist_mv_def init_tuple_def 
                by auto
              ultimately have "as \<in> hist_sat \<union> {as \<in> snd db. case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False}"
                using assm db_props
                unfolding hist_sat_mv_def
                by auto
              moreover {
                assume "as \<in> hist_sat"
                then have "\<forall>(t, r)\<in>set (linearize data_in). as \<in> r" using tuple_init_props_hist_sat by auto
                then have "as \<in> r" using list_mem by auto
              }
              moreover {
                assume "as \<in> {as \<in> snd db. case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False}"
                then have "as \<in> snd db" "(case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False)"
                  by auto
                then obtain idx where idx_props: "Mapping.lookup tuple_since_hist as = Some idx" "idx \<le> idx_oldest_mv []"
                  using case_optionE
                  by blast
                then have "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
                  using tuple_init_props
                  by (auto split: option.splits)
                then have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest) (linearize data_in)). as \<in> y)"
                  unfolding tuple_since_tp_def
                  by auto
                then have "(\<forall>(t, y)\<in>set (drop (idx_oldest_mv [] - idx_oldest) (linearize data_in)). as \<in> y)"
                  using idx_props(2)
                  by (meson diff_le_mono set_drop_subset_set_drop subsetD)
                then have "(\<forall>(t, y)\<in>set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)). as \<in> y)"
                  using data_sorted[OF assms(1)] drop_filter_memR[of "linearize data_in" "args_ivl args" nt]
                  unfolding idx_oldest_mv_def
                  by auto
                then have "as \<in> r" using list_mem by auto
              }
              ultimately have "as \<in> r" by auto
            }
            then show ?thesis by auto
          qed
          then have "((lin_data_in''_mv []) \<noteq> []) \<and> (
            \<forall>(t, r) \<in> set (lin_data_in''_mv []). as \<in> r
          )" using non_empty by auto
        }
        moreover {
          assume assm:
            "((lin_data_in''_mv []) \<noteq> [])" 
            "\<forall>(t, r) \<in> set (lin_data_in''_mv []). as \<in> r"
          then obtain db dbs where db_props: "lin_data_in''_mv [] = db # dbs"
            using list.exhaust
            by blast
          then have db_in: "db \<in> set (linearize data_in)"
            by (metis db_props in_set_dropD lin_data_in''_eq list.set_intros(1))
          have db_mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) db"
            using db_props
            unfolding lin_data_in''_mv_def data_in'_eq
            by (metis (no_types, lifting) append_Nil2 filter.simps(1) list.set_intros(1) list.simps(8) mem_Collect_eq set_filter)
          from assm(2) have all_relR: "\<forall>(t, r) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)). as \<in> r"
            unfolding lin_data_in''_mv_def data_in'_eq
            by auto

          have db_relR: "as \<in> snd db"
            using db_props assm(2)
            by auto

          have in_nonempty: "linearize data_in \<noteq> []" using assm(1) unfolding lin_data_in''_mv_def data_in'_eq by auto

          define l where "l = drop (length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))) (linearize data_in)"
          define in_but_last where "in_but_last = (take (length (linearize data_in) - 1) (linearize data_in))"

          have l_props: "l \<noteq> []"
               "\<forall>(t, r)\<in>set l. as \<in> r"
            using assm data_sorted[OF assms(1)] drop_filter_memR[of "linearize data_in" "args_ivl args" nt]
            unfolding lin_data_in''_mv_def data_in'_eq l_def
            by auto
          then have last_l_mem: "last (linearize data_in) \<in> set l"
            unfolding l_def
            by (metis drop_eq_Nil last_drop last_in_set leI)
          then have last_relR: "as \<in> snd (last (linearize data_in))"
            using l_props(2)
            by auto
          have data_in_split: "linearize data_in = in_but_last @ [last (linearize data_in)]"
            using in_nonempty
                  drop_last[of "linearize data_in"]
            unfolding in_but_last_def
            by (metis append_butlast_last_id butlast_conv_take)

          {
            assume assm_all: "\<forall>(t, r) \<in> set in_but_last. as \<in> r"
            then have "\<forall>(t, r) \<in> set (linearize data_in). as \<in> r"
              using assm_all l_props(2) data_in_split last_l_mem
              by (metis in_set_simps(4) list_appendE set_ConsD)
            then have "as \<in> hist_sat" using tuple_init_props_hist_sat in_nonempty is_empty_alt
              by auto
          }
          moreover {
            define A where "A = {i \<in> {0..<length (linearize data_in) - 1}. as \<notin> snd ((linearize data_in)!i)}"
            define j where "j = Max A"
            assume "\<exists>(t, r) \<in> set in_but_last. as \<notin> r"
            then obtain i where "i \<in> {0..<length (linearize data_in) - 1}" "as \<notin> snd ((linearize data_in)!i)"
              unfolding in_but_last_def
              by (metis (no_types, lifting) case_prodE diff_le_self imageE nth_image snd_conv)
            then have "i \<in> A" unfolding A_def by auto
            then have A_props: "A \<noteq> {}" "finite A" unfolding A_def by auto
            then have "j \<in> A" unfolding j_def by auto
            then have j_props: "j \<in> {0..<length (linearize data_in) - 1}" "as \<notin> snd ((linearize data_in)!j)"
              unfolding A_def
              by auto
            then have j_l: "(idx_oldest + j + 1) < idx_mid"
              using data_in_len
              by auto
            {
              assume "j + 1 > length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
              then have j_geq: "j \<ge> length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
                by auto
              moreover have "filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in) = takeWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)"
                using data_sorted[OF assms(1)] sorted_filter_takeWhile_not_memR[of "linearize data_in" args nt]
                by auto
              moreover have "linearize data_in = (takeWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) @ (dropWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
                by auto
              ultimately have "((linearize data_in)!j) = (dropWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))!(j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)))"
                using j_props(1) idx_append_snd[of j "(takeWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))" "linearize data_in" "(dropWhile (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"]
                by auto
              then have jth: "((linearize data_in)!j) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)!(j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)))"
                using data_sorted[OF assms(1)] sorted_filter_dropWhile_memR[of "linearize data_in" args nt]
                by auto
              have "j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) \<in> {0..<length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))}"
                using j_geq j_props(1) sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(linearize data_in)"]
                by (auto simp add: filter_simp)
              then have "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)!(j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))"
                using nth_set_member[of "j - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))" "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)"]
                by auto
              then have "as \<in> snd ((linearize data_in)!j)"
                using jth all_relR
                by auto
              then have "False" using j_props(2) by auto
            }
            then have j_suc_leq: "j + 1 \<le> length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in))"
              using not_le_imp_less
              by blast
            {
              fix t y
              assume "(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) (linearize data_in))"
              then have assm: "(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) (in_but_last @ [last (linearize data_in)]))"
                using data_in_split
                by auto
              have "as \<in> y"
              proof (cases "(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) in_but_last)")
                case True
                then obtain k' where k'_props: "k' \<in> {0..<length in_but_last - j - 1}" "(drop (j+1) in_but_last)!k' = (t, y)"
                  by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right atLeastLessThan_iff diff_add_inverse diff_diff_left in_set_conv_nth leI length_drop not_less_zero)
                
                define k where "k = k' + j + 1"
                have "in_but_last!k = (t, y)" "k \<in> {j+1..<length in_but_last}"
                  using k'_props j_props(1)
                  unfolding k_def
                  by (auto simp add: add.commute)
                then have k_props: "(linearize data_in)!k = (t, y)" "k \<in> {j+1..<length (linearize data_in) - 1}"
                  unfolding in_but_last_def
                  by auto
                {
                  assume "as \<notin> y"
                  then have "k \<in> A" using k_props unfolding A_def by auto
                  then have "k \<le> j" using A_props unfolding j_def by auto
                  then have "False" using k_props(2) by auto
                }
                then show ?thesis by auto
              next
                case False
                {
                  assume "(t, y) \<noteq> last (linearize data_in)"
                  then have "(t, y) \<notin> set (drop ((idx_oldest + j + 1) - idx_oldest) (in_but_last @ [last (linearize data_in)]))"
                    using False
                    using in_set_dropD
                    by fastforce
                  then have "False"
                    using assm
                    by auto
                }
                then have "(t, y) = last (linearize data_in)" using assm by auto
                then show ?thesis
                  using last_relR
                  by (metis snd_conv)
              qed
            }
            then have all_relR: "(\<forall>(t, y)\<in>set (drop ((idx_oldest + j + 1) - idx_oldest) (linearize data_in)). as \<in> y)"
              by auto

            moreover have "as \<notin> snd (linearize data_in ! ((idx_oldest + j + 1) - idx_oldest - 1))"
              using j_props(2)
              by auto

            ultimately have tp: "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid (idx_oldest + j + 1)"
              using in_nonempty j_l
              unfolding tuple_since_tp_def
              by auto
            then obtain idx where idx_props:
              "Mapping.lookup tuple_since_hist as = Some idx"
              "tuple_since_tp args as (linearize data_in) idx_oldest idx_mid idx"
              using tuple_init_props
              by (auto split: option.splits)
            then have "idx = (idx_oldest + j + 1)"
              using tuple_since_hist_lookup_eq[OF tuple_init_props tp _ data_in_len]
              by auto                              
            moreover have "idx_oldest + j + 1 \<le> idx_oldest_mv []"
              using j_suc_leq
              unfolding idx_oldest_mv_def
              by auto
            ultimately have "as \<in> {as \<in> snd db. case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False}"
              using db_relR idx_props(1)
              unfolding idx_oldest_mv_def
              by auto
          }

          ultimately have "as \<in> hist_sat \<union> {as \<in> snd db. case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx \<le> idx_oldest_mv [] | None \<Rightarrow> False}"
            by auto
          then have "as \<in> (hist_sat_mv [] init_tuple)"
            using assm(1) db_props Nil(1)
            unfolding hist_sat_mv_def init_tuple_def tuple_since_hist_mv_def
            by (auto split: list.splits)
        }
        ultimately show ?thesis
          by blast
      qed
      moreover have "(as \<in> (since_sat_mv [] init_tuple) \<longrightarrow>
        ((as \<in> (hist_sat_mv [] init_tuple)) \<or> tuple_since_lhs as (lin_data_in''_mv []) args maskL (lin_data_in''_aux_mv []))
      )"
      proof -
        {
          assume "as \<in> (since_sat_mv [] init_tuple)"
          then have since_mem: "idx_mid_mv [] \<noteq> idx_oldest_mv []"
                    "as \<in> since_sat"
            unfolding since_sat_mv_def init_tuple_def
            by (auto split: if_splits)
          then have non_empty: "lin_data_in''_mv [] \<noteq> []"
            using mv_ln_eq
            by (metis add_cancel_left_left list.size(3))

          from assms(1) have in_eq: "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
            by auto

          from assms(1) have auxlist_props: "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db))"
            by auto
          then have in_memR: "\<forall>db\<in>set (auxlist_data_in args mt auxlist). memR (args_ivl args) (mt - time db)"
            unfolding auxlist_data_in_def
            by auto

          have "as \<in> hist_sat \<or> tuple_since_lhs as (linearize data_in) args maskL (auxlist_data_in args mt auxlist)"
            using since_mem tuple_init_props_since(1)
            by auto
          moreover {
            assume "as \<in> hist_sat"
            then have "\<forall>(t, r)\<in>set (linearize data_in). as \<in> r"
              using tuple_init_props_hist_sat
              by auto
            then have "\<forall>(t, r)\<in>set (lin_data_in''_mv []). as \<in> r"
              unfolding lin_data_in''_mv_def data_in'_eq
              by auto
            then have "as \<in> (hist_sat_mv [] init_tuple)"
              using non_empty hist_sat_props
              by auto
          }
          moreover {
            assume "tuple_since_lhs as (linearize data_in) args maskL (auxlist_data_in args mt auxlist)"
            then obtain n where n_props:
              "n\<in>{0..<length (linearize data_in)}"
              "let suffix = drop n (auxlist_data_in args mt auxlist) in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL as)"
              "linearize data_in \<noteq> []"
              unfolding tuple_since_lhs_def
              by auto
            then have n_l: "n < length (auxlist_data_in args mt auxlist)"
              using auxlist_eqs(2)
              by (metis atLeastLessThan_iff in_eq length_map)
            define suffix where "suffix = drop n (auxlist_data_in args mt auxlist)"
            
            have sorted_auxlist: "sorted (map fst auxlist)" using assms(1) by auto
            then have sorted_in: "sorted (map fst (auxlist_data_in args mt auxlist))"
              unfolding suffix_def auxlist_data_in_def
              by (metis (no_types, lifting) sorted_filter)


            then have suffix_props:
              "(\<forall>(t, l, y)\<in>set suffix. as \<in> y)"
              "join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL as)"
              "suffix \<noteq> []"
              using n_props n_l
              unfolding suffix_def
              by (auto simp add: Let_def)

            moreover have hd_suffix: "hd suffix = (auxlist_data_in args mt auxlist)!n"
              using suffix_props(3)
              unfolding suffix_def
              by (simp add: hd_drop_conv_nth)

            ultimately have relL: "join_cond (args_pos args) (relL ((auxlist_data_in args mt auxlist)!n)) (proj_tuple maskL as)"
              by auto

            {
              define l where "l = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist))"
              assume assm: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist)!n)"
              have "lin_data_in''_aux_mv [] = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)"
                using auxlist_eqs(2)
                unfolding lin_data_in''_aux_mv_def data_in'_aux_def
                by auto
              then have lin_data_in''_eq: "lin_data_in''_aux_mv [] = drop l (auxlist_data_in args mt auxlist)"
                using drop_filter_memR[OF sorted_in, of "args_ivl args" nt]
                unfolding l_def
                by auto

              define n' where "n' = n - l"
              {
                assume "l > n"
                then have "((auxlist_data_in args mt auxlist)!n) \<in> set (take l (auxlist_data_in args mt auxlist))"
                  using n_l n_props(1) 
                  by (metis atLeastLessThan_iff image_eqI nat_le_linear nth_image take_all)
                then have "((auxlist_data_in args mt auxlist)!n) \<in> set (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist))"
                  using take_filter_not_memR[OF sorted_in, of "args_ivl args" nt]
                  unfolding l_def
                  by auto
                then have "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist)!n)"
                  by auto
                then have "False"
                  using assm
                  by auto
              }
              then have l_leq: "l \<le> n" using not_le_imp_less by blast
              then have "\<forall>(t, l, r)\<in>set (drop (n-l) (drop l (auxlist_data_in args mt auxlist))). as \<in> r"
                using suffix_props(1) n_l
                unfolding suffix_def
                by auto
              then have "\<forall>(t, l, r)\<in>set (drop (n-l) (lin_data_in''_aux_mv [])). as \<in> r"
                using lin_data_in''_eq
                by auto
              moreover have "join_cond (args_pos args) (relL (hd (drop (n-l) (lin_data_in''_aux_mv [])))) (proj_tuple maskL as)"
                using lin_data_in''_eq l_leq suffix_props(2)
                unfolding suffix_def
                by auto
              ultimately have "(
                let suffix = drop n' (lin_data_in''_aux_mv [])
                in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL as))"
                by (simp only: Let_def n'_def)
              moreover have "n'\<in>{0..<length (lin_data_in''_mv [])}"
                unfolding n'_def
                using n_l lin_data_in''_eq l_leq data_in''_aux_eq
                by (metis (mono_tags) atLeastLessThan_iff diff_less_mono length_drop length_map zero_le)
              ultimately have "tuple_since_lhs as (lin_data_in''_mv []) args maskL (lin_data_in''_aux_mv [])"
                using non_empty
                unfolding tuple_since_lhs_def
                by blast
            }
            moreover {
              assume assm: "\<not>(\<lambda>(t, _). memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist)!n)"
              {
                fix t r
                assume "(t, r) \<in> set (lin_data_in''_mv [])"
                then have data_in_mem: "(t, r) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in))"
                  unfolding lin_data_in''_mv_def data_in'_eq
                  by auto
                then have memR: "memR (args_ivl args) (nt - t)" by auto

                have filter_simp: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) = ((\<lambda>(t, _). memR (args_ivl args) (nt - t)) \<circ> (\<lambda>(t, l, r). (t, r)))"
                  by auto

                have "map (\<lambda> (t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)"
                  using in_eq filter_map[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda> (t, l, r). (t, r))" "(auxlist_data_in args mt auxlist)"]
                  by (auto simp add: filter_simp)
                then have "(t, r) \<in> set (map (\<lambda> (t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)))"
                  using data_in_mem
                  by auto
                then obtain l where tlr_mem: "(t, l, r) \<in> set (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist))"
                  by auto
                then have mem: "mem (args_ivl args) (mt - t)"
                  using nt_mono(1) time
                  unfolding auxlist_data_in_def
                  by auto
                then have "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
                  using tlr_mem
                  unfolding auxlist_data_in_def
                  by auto
                then obtain i where i_props:
                  "i \<in> {0..<length(auxlist_data_in args mt auxlist)}"
                  "(auxlist_data_in args mt auxlist)!i = (t, l, r)"
                  by (meson atLeastLessThan_iff nth_the_index the_index_bounded zero_le)
                {
                  assume "i \<le> n"
                  then have "t \<le> fst ((auxlist_data_in args mt auxlist)!n)"
                    using i_props(2) sorted_in n_l
                    by (smt fst_conv le_less_trans length_map nth_map sorted_iff_nth_mono)
                  then have "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist)!n)"
                    using memR memR_antimono[of "args_ivl args"]
                    by auto
                  then have "False" using assm by blast
                }
                then have "i > n" using not_le_imp_less by blast
                then have "(t, l, r) \<in> set suffix"
                  using i_props
                  unfolding suffix_def
                  by (metis atLeastLessThan_iff in_set_conv_nth le_add_diff_inverse length_drop less_imp_le_nat n_l nat_add_left_cancel_less nth_drop)
                then have "as \<in> r" using suffix_props by auto
              }
              then have "\<forall>(t, r)\<in>set (lin_data_in''_mv []). as \<in> r" by auto
              then have "as \<in> (hist_sat_mv [] init_tuple)"
                using non_empty hist_sat_props
                by auto
            }

            ultimately have "((as \<in> (hist_sat_mv [] init_tuple)) \<or> tuple_since_lhs as (lin_data_in''_mv []) args maskL (lin_data_in''_aux_mv []))"
              by fast
          }
          ultimately have "((as \<in> (hist_sat_mv [] init_tuple)) \<or> tuple_since_lhs as (lin_data_in''_mv []) args maskL (lin_data_in''_aux_mv []))"
            by blast
        }
        then show ?thesis by auto
      qed
      moreover have "(tuple_since_lhs as (lin_data_in''_mv []) args maskL (lin_data_in''_aux_mv []) \<longrightarrow>
        as \<in> (since_sat_mv [] init_tuple)
      )"
      proof -
        {
          assume assm: "tuple_since_lhs as (lin_data_in''_mv []) args maskL (lin_data_in''_aux_mv [])"
          then have non_empty: "lin_data_in''_mv [] \<noteq> []"
            unfolding tuple_since_lhs_def
            by auto
          
          have sorted_auxlist: "sorted (map fst auxlist)" using assms(1) by auto
          then have sorted_in: "sorted (map fst (auxlist_data_in args mt auxlist))"
            unfolding auxlist_data_in_def
            by (metis (no_types, lifting) sorted_filter)

          define l where "l = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist))"

          have "lin_data_in''_aux_mv [] = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)"
            using auxlist_eqs(2)
            unfolding lin_data_in''_aux_mv_def data_in'_aux_def
            by auto
          then have lin_data_in''_eq: "lin_data_in''_aux_mv [] = drop l (auxlist_data_in args mt auxlist)"
            using drop_filter_memR[OF sorted_in, of "args_ivl args" nt]
            unfolding l_def
            by auto

          moreover obtain n where n_props:
            "n\<in>{0..<length (lin_data_in''_mv [])}"
            "let suffix = drop n (lin_data_in''_aux_mv []) in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL as)"
            using assm
            unfolding tuple_since_lhs_def
            by auto

          ultimately have "let suffix = drop (l+n) (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and>
            join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL as)
          )"
            by (simp add: add.commute)

          moreover have "l + n < length (linearize data_in)"
            using n_props data_in''_aux_eq lin_data_in''_eq in_eq
            by (smt add.commute atLeastLessThan_iff drop_drop length_drop length_map zero_less_diff)

          ultimately have "tuple_since_lhs as (linearize data_in) args maskL (auxlist_data_in args mt auxlist)"
            using non_empty
            unfolding tuple_since_lhs_def
            by fastforce
          then have "as \<in> since_sat"
            using tuple_init_props_since(2)
            by auto
          then have "as \<in> (since_sat_mv [] init_tuple)"
            using mv_ln_eq non_empty
            unfolding since_sat_mv_def init_tuple_def
            by (metis List.fold_simps(1) add_cancel_left_left comp_apply length_0_conv snd_conv)
        }
        then show ?thesis by auto
      qed
      moreover have "get_idx_move (fold fold_op_f [] init_tuple) = idx_mid_mv []"
        unfolding get_idx_move_def init_tuple_def idx_mid_mv_def
        by auto
      moreover have "(case Mapping.lookup (fst (fold fold_op_f [] init_tuple)) as of Some idx \<Rightarrow> idx < idx_mid_mv [] | None \<Rightarrow> True)"
      proof -
        have "fst (fold fold_op_f [] init_tuple) = tuple_since_hist" unfolding init_tuple_def by auto
        moreover have "idx_mid_mv [] = idx_mid" unfolding idx_mid_mv_def by auto
        moreover have "(case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow> idx < idx_mid | None \<Rightarrow> True)"
          using tuple_init_props
          unfolding tuple_since_tp_def
          by (auto split: option.splits)
        ultimately show ?thesis by auto
      qed
      ultimately show ?case by auto
    next
      case (snoc x xs)
      have assm:
        "length (lin_data_in''_mv (xs @ [x])) + idx_oldest_mv (xs @ [x]) = idx_mid_mv (xs @ [x])"
        using snoc
        by auto
      define r where "r = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (xs @ [x]))"
      have r_leq: "r \<le> length (xs @ [x])"
        unfolding r_def
        using length_filter_le[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(xs @ [x])"]
        by auto
      define r' where "r' = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs)"
      have r'_leq: "r' \<le> length xs"
        unfolding r'_def
        using length_filter_le[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "xs"]
        by auto


      have "length (linearize data_in') + idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + length xs = idx_mid_mv xs"
        using assm(1) r_leq snoc(2)
        unfolding lin_data_in''_mv_def idx_mid_mv_def idx_oldest_mv_def r_def
        by (auto simp add: case_prod_beta')
      then have "length (linearize data_in') + r' + (idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + length xs - r') = idx_mid_mv xs"
        using r'_leq
        unfolding idx_mid_mv_def
        by auto
      
      then have "length (lin_data_in''_mv xs) + idx_oldest_mv xs = idx_mid_mv xs"
        using snoc(2)
        unfolding r'_def idx_oldest_mv_def lin_data_in''_mv_def
        by auto
      moreover have xs_sorted: "sorted (map fst xs)"
        using snoc(3)
        by (simp add: sorted_append)
      moreover have xs_ts: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set xs. t < t'"
        using snoc(4)
        by auto
      moreover have "\<forall>(t, l, r) \<in> set xs. table (args_n args) (args_L args) l \<and> table (args_n args) (args_R args) r"
        using snoc(5)
        by auto
      ultimately have IH: "case Mapping.lookup (tuple_since_hist_mv xs init_tuple) as of
          None   \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx
        | Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
        "get_idx_move (fold fold_op_f xs init_tuple) = idx_mid_mv xs"
        "(case Mapping.lookup (fst (fold fold_op_f xs init_tuple)) as of None \<Rightarrow> True | Some idx \<Rightarrow> idx < idx_mid_mv xs)"
        "as \<in> (hist_sat_mv xs init_tuple) \<longleftrightarrow>
          ((lin_data_in''_mv xs) \<noteq> []) \<and> (
            \<forall>(t, r) \<in> set (lin_data_in''_mv xs). as \<in> r
        )"
        "(as \<in> since_sat_mv xs init_tuple \<longrightarrow> as \<in> hist_sat_mv xs init_tuple \<or> tuple_since_lhs as (lin_data_in''_mv xs) args maskL (lin_data_in''_aux_mv xs))"
        "(tuple_since_lhs as (lin_data_in''_mv xs) args maskL (lin_data_in''_aux_mv xs) \<longrightarrow> as \<in> since_sat_mv xs init_tuple)"
        using snoc(1)
        by auto

      define tuple where "tuple = (fold fold_op_f xs init_tuple)"
      define tuple_since_hist' where "tuple_since_hist' = fst tuple"
      define joined_mapping where "joined_mapping = Mapping.filter (\<lambda>as _. as \<in> (relR x)) tuple_since_hist'"

      have fold_IH_since_hist: "fst (fold_op_f x tuple) = upd_set joined_mapping (\<lambda>_. (get_idx_move tuple)) ((relR x) - Mapping.keys joined_mapping)"
        unfolding fold_op_f_def relR_def relL_def joined_mapping_def get_idx_move_def tuple_since_hist'_def
        by (auto simp add: Let_def case_prod_beta')

      define hist_sat' where "hist_sat' = (fst o snd) tuple"
      have fold_IH_hist_sat: "(fst o snd) (fold_op_f x tuple) = hist_sat' \<inter> (relR x)"
        unfolding fold_op_f_def relR_def hist_sat'_def
        by (auto simp add: Let_def case_prod_beta')

      have x_table:
        "table (args_n args) (args_L args) (relL x)"
        "table (args_n args) (args_R args) (relR x)"
        using snoc(5)
        unfolding relL_def relR_def
        by (auto)

      have maskL_eq: "maskL = join_mask (args_n args) (args_L args)"
        using assms(1)
        by auto

      define since_sat' where "since_sat' = (snd o snd o snd) tuple"
      have fold_IH_since_sat: "(snd o snd o snd) (fold_op_f x tuple) = (since_sat' \<inter> (relR x)) \<union> proj_tuple_in_join_optim (args_pos args) (relR x) (join_mask (args_n args) (args_R args)) (relL x) (join_mask (args_n args) (args_L args))"
        unfolding fold_op_f_def relR_def relL_def since_sat'_def
        by (auto simp add: Let_def case_prod_beta')
      then have fold_IH_since_sat: "(snd o snd o snd) (fold_op_f x tuple) = (since_sat' \<inter> (relR x)) \<union> {as \<in> (relR x). proj_tuple_in_join (args_pos args) maskL as (relL x)}"
        using proj_tuple_in_join_optim_equiv[OF x_table, of "args_pos args"] maskL_eq
        by blast

      {
        assume non_empty: "lin_data_in''_mv (xs @ [x]) \<noteq> []"
        assume mem: "\<not> (\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
        {
          fix db
          assume "db \<in> set xs"
          then have "fst db \<le> fst x"
            using snoc(3)
            by (simp add: sorted_append)
          then have  "\<not> (\<lambda>(t, _). memR (args_ivl args) (nt - t)) db"
            using mem memR_antimono
            by auto
        }
        moreover {
          fix db
          assume "db \<in> set (linearize data_in)"
          then have "fst db < fst x"
            using snoc(4)
            by auto
          then have "\<not> (\<lambda>(t, _). memR (args_ivl args) (nt - t)) db"
            using mem memR_antimono
            by auto
        }
        ultimately have "lin_data_in''_mv (xs @ [x]) = []"
          using mem
          unfolding lin_data_in''_mv_def data_in'_eq
          by auto
        then have "False" using non_empty by auto
      }
      then have mem: "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<longrightarrow> (\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
        by auto

      have tuple_since_hist_mv_props: "(case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of
        None    \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx
       | Some idx \<Rightarrow> tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx)"
      proof (cases "(idx_mid_mv (xs @ [x])) = (idx_oldest_mv (xs @ [x]))")
        case True
        then have "tuple_since_hist_mv (xs @ [x]) init_tuple = Mapping.empty"
          unfolding tuple_since_hist_mv_def
          by auto
        then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = None"
          by (simp add: Mapping.empty_def Mapping.lookup.abs_eq)
        moreover have "\<forall>idx. \<not>tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
          using True snoc
          unfolding tuple_since_tp_def
          by auto
        ultimately show ?thesis by auto
      next

        case non_empty: False
        
        then have "tuple_since_hist_mv (xs @ [x]) init_tuple = fst (fold fold_op_f (xs @ [x]) init_tuple)"
          unfolding tuple_since_hist_mv_def
          by auto
        then have "tuple_since_hist_mv (xs @ [x]) init_tuple = fst (fold_op_f x tuple)"
          using fold_alt[of fold_op_f "xs" "x" init_tuple]
          unfolding tuple_def
          by auto              
        then have mapping_eq: "tuple_since_hist_mv (xs @ [x]) init_tuple = upd_set joined_mapping (\<lambda>_. (get_idx_move tuple)) ((relR x) - Mapping.keys joined_mapping)"
          using fold_IH_since_hist
          by auto
        
        have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
          using mem non_empty snoc(2)
          by auto

        have data_in''_eq: "(lin_data_in''_mv (xs @ [x])) = lin_data_in''_mv (xs) @ [(\<lambda>(t, l, y). (t, y)) x]"
          using mem
          unfolding lin_data_in''_mv_def
          by simp

        have data_in''_last: "last (lin_data_in''_mv (xs @ [x])) = (\<lambda>(t, l, y). (t, y)) x"
          using mem snoc(2)
          unfolding lin_data_in''_mv_def
          by (simp add: Suc_le_lessD take_Suc_conv_app_nth)

        show ?thesis
        proof (cases "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as")
          case None
          then have not_mem: "as \<notin> ((relR x) - Mapping.keys joined_mapping)"
            using mapping_eq
            by (metis Mapping_lookup_upd_set option.discI)
          then have "as \<notin> (relR x) \<or> as \<in> Mapping.keys joined_mapping"
            by auto
          moreover have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
            using not_mem mapping_eq
            by (metis Mapping_lookup_upd_set)
          ultimately have not_relR: "as \<notin> (relR x)"
            by (simp add: None keys_is_none_rep)
          {
            fix idx
            assume "idx < idx_mid_mv (xs @ [x])"
            then have "last (lin_data_in''_mv (xs @ [x])) \<in> set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x])))"
              using snoc(2) non_empty
              by (smt add_cancel_left_left diff_is_0_eq dual_order.strict_iff_order last_drop last_in_set leI length_drop length_greater_0_conv less_diff_conv2)
            moreover have "as \<notin> snd (last (lin_data_in''_mv (xs @ [x])))"
            using not_relR data_in''_last
              unfolding relR_def
              by (simp add: case_prod_beta')
            ultimately have "\<not>(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y)"
              by fastforce
          }
          then have "\<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
            unfolding tuple_since_tp_def
            by auto
          then show ?thesis
            using None
            by simp
        next
          case (Some idx)

          have data_in_nonempty: "lin_data_in''_mv (xs @ [x]) \<noteq> []"
            using snoc(2) non_empty
            by auto

          have idx_oldest_eq: "idx_oldest_mv (xs @ [x]) = idx_oldest_mv (xs)"
            using mem
            unfolding idx_oldest_mv_def
            by auto
          
          show ?thesis
          proof (cases "idx_mid_mv xs = idx_oldest_mv xs")
            case True
            then have IH_none: "Mapping.lookup (tuple_since_hist_mv xs init_tuple) as = None"
              unfolding tuple_since_hist_mv_def
              by (simp add: Mapping.lookup_empty)
            then have "\<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
              using IH_none IH(1)
              by auto

            have "(lin_data_in''_mv xs) = []"
              using mv_ln_eq True
              by (metis Ex_list_of_length append_Nil append_eq_append_conv length_append)
            then have data_in''_eq: "(lin_data_in''_mv (xs @ [x])) = [(\<lambda>(t, l, y). (t, y)) x]"
              using data_in''_eq
              by auto

            show ?thesis
            proof (cases "as \<in> (relR x - Mapping.keys joined_mapping)")
              case mem: True
              then have "as \<in> relR x" by auto
              then have relR: "as \<in> snd ((\<lambda>(t, l, y). (t, y)) x)"
                unfolding relR_def
                by (simp add: case_prod_beta')

              have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some (get_idx_move tuple)"
                using mapping_eq mem
                by (simp add: Mapping_lookup_upd_set)
              then have idx_eq: "idx = idx_mid_mv xs"
                using Some IH(2)
                unfolding get_idx_move_def tuple_def
                by auto
              then have "idx < idx_mid_mv (xs @ [x])"
                unfolding idx_mid_mv_def
                by auto
              moreover have idx_eq': "(idx_oldest_mv (xs @ [x])) = idx"
                using idx_oldest_eq True idx_eq
                by auto
              moreover have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y)"
                using idx_eq' data_in''_eq relR
                by auto
              ultimately have "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
                using data_in_nonempty
                unfolding tuple_since_tp_def
                by auto
              then show ?thesis using Some by auto
            next
              case False
              then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
                using mapping_eq
                by (metis Mapping_lookup_upd_set)
              then have "as \<in> relR x"
                unfolding joined_mapping_def
                by (metis Mapping_lookup_filter_Some_P Some)
              then have relR: "as \<in> snd ((\<lambda>(t, l, y). (t, y)) x)"
                unfolding relR_def
                by (simp add: case_prod_beta')

              have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup tuple_since_hist' as"
                using Mapping_lookup_filter_not_None Some lookup_eq
                unfolding joined_mapping_def
                by fastforce
              then have idx_leq: "idx \<le> idx_mid_mv xs"
                using IH(3) Some
                unfolding tuple_since_hist'_def tuple_def
                by (auto split: option.splits)
              then have "idx < idx_mid_mv (xs @ [x])"
                unfolding idx_mid_mv_def
                by auto
              moreover have idx_leq': "idx \<le> (idx_oldest_mv (xs @ [x]))"
                using idx_oldest_eq True idx_leq
                by auto
              moreover have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y)"
                using idx_leq' data_in''_eq relR
                by auto
              ultimately have "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
                using data_in_nonempty
                unfolding tuple_since_tp_def
                by auto
              then show ?thesis using Some by auto
            qed
          next
            case IH_nonempty: False
            moreover have idx_leq: "idx < idx_mid_mv (xs @ [x])"
            proof -
              show ?thesis
              proof (cases "as \<in> ((relR x) - Mapping.keys joined_mapping)")
                case True
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some (get_idx_move tuple)"
                  using mapping_eq
                  by (simp add: Mapping_lookup_upd_set)
                then have "idx = get_idx_move tuple"
                  using Some
                  by auto
                then have "idx = idx_mid_mv xs"
                  using IH(2)
                  unfolding tuple_def
                  by auto
                then show ?thesis
                  unfolding idx_mid_mv_def
                  by auto
              next
                case False
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
                  using mapping_eq
                  by (metis Mapping_lookup_upd_set)
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup tuple_since_hist' as"
                  unfolding joined_mapping_def
                  using Some Mapping_lookup_filter_not_None
                  by force
                then have "Mapping.lookup (fst (fold fold_op_f xs init_tuple)) as = Some idx"
                  unfolding tuple_since_hist'_def tuple_def
                  using Some
                  by auto
                then have "tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
                  using IH(1) IH_nonempty
                  unfolding tuple_since_hist_mv_def
                  by auto
                then have "idx \<le> idx_mid_mv xs"
                  unfolding tuple_since_tp_def
                  by auto
                then show ?thesis unfolding idx_mid_mv_def by auto
              qed
            qed
            moreover have "\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y"
            proof -
              show ?thesis
              proof (cases "as \<in> ((relR x) - Mapping.keys joined_mapping)")
                case True
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some (get_idx_move tuple)"
                  using mapping_eq
                  by (simp add: Mapping_lookup_upd_set)
                then have "idx = get_idx_move tuple"
                  using Some
                  by auto
                then have "idx + 1 = idx_mid_mv (xs @ [x])"
                  using IH(2)
                  unfolding tuple_def idx_mid_mv_def
                  by auto
                then have "idx + 1 = length (lin_data_in''_mv (xs @ [x])) + idx_oldest_mv (xs @ [x])"
                  using snoc(2)
                  by linarith
                then have "drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x])) = [(\<lambda>(t, l, y). (t, y)) x]"
                  using data_in''_last drop_last[of "lin_data_in''_mv (xs @ [x])"] data_in_nonempty
                  by (simp add: data_in''_eq)
                moreover have "as \<in> (relR x)"
                  using True
                  by auto
                ultimately show ?thesis
                  unfolding relR_def
                  by (auto simp add: case_prod_beta')
              next
                case not_mem: False
                then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
                    using not_mem mapping_eq
                    by (metis Mapping_lookup_upd_set)
                have "as \<notin> (relR x) \<or> as \<in> Mapping.keys joined_mapping" using not_mem by auto
                moreover {
                  assume "as \<notin> (relR x)"
                  then have "Mapping.lookup joined_mapping as = None"
                    unfolding joined_mapping_def
                    using Mapping_keys_filterD keys_dom_lookup
                    by fastforce
                  then have "False" using lookup_eq Some by auto
                }
                ultimately have "as \<in> Mapping.keys joined_mapping" by blast
                then have relR: "as \<in> relR x"
                  unfolding joined_mapping_def
                  by (meson Mapping_keys_filterD)
                then have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup tuple_since_hist' as"
                  using lookup_eq
                  unfolding joined_mapping_def
                  by (simp add: Mapping_lookup_filter_Some)
                then have "tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
                  using IH(1) Some IH_nonempty
                  unfolding tuple_since_hist'_def tuple_def tuple_since_hist_mv_def
                  by (auto split: option.splits)
                then have IH_hist: "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv xs) (lin_data_in''_mv xs)). as \<in> y)"
                  unfolding tuple_since_tp_def
                  by (auto)
                have "idx_oldest_mv (xs @ [x]) = idx_oldest_mv (xs)"
                  using mem
                  unfolding idx_oldest_mv_def
                  by auto
                moreover have "lin_data_in''_mv (xs @ [x]) = (lin_data_in''_mv (xs)) @ [(\<lambda>(t, l, y). (t, y)) x]"
                  using mem
                  unfolding lin_data_in''_mv_def
                  by auto
                moreover have "(idx - idx_oldest_mv (xs @ [x])) < length (lin_data_in''_mv (xs @ [x]))"
                  using idx_leq snoc(2) non_empty
                  by linarith
                ultimately have list_eq: "drop (idx - idx_oldest_mv xs) (lin_data_in''_mv xs) @ [(\<lambda>(t, l, y). (t, y)) x] = (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x])))"
                  by auto

                have "as \<in> snd ((\<lambda>(t, l, y). (t, y)) x)"
                  using relR
                  unfolding relR_def
                  by (auto simp add: case_prod_beta')
                then have "(\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv xs) (lin_data_in''_mv xs) @ [(\<lambda>(t, l, y). (t, y)) x]). as \<in> y)"
                  using IH_hist
                  by auto

                then show ?thesis
                  using list_eq
                  by auto
              qed
            qed
            moreover have "idx_oldest_mv (xs @ [x]) < idx \<Longrightarrow> as \<notin> snd (lin_data_in''_mv (xs @ [x]) ! (idx - idx_oldest_mv (xs @ [x]) - 1))"
            proof -
              assume assm: "idx_oldest_mv (xs @ [x]) < idx"
              then have "idx_oldest_mv (xs) < idx" using idx_oldest_eq by auto
              show ?thesis
              proof (cases "as \<in> ((relR x) - Mapping.keys joined_mapping)")
                case True
                then have "as \<in> relR x" "as \<notin> Mapping.keys joined_mapping" by auto
                then have "Mapping.lookup tuple_since_hist' as = None"
                  unfolding joined_mapping_def
                  by (meson Mapping_keys_filterI option.exhaust)
                then have tuple_since_tp: "\<forall>idx. \<not> tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
                  using IH(1) IH_nonempty
                  unfolding tuple_since_hist'_def tuple_def tuple_since_hist_mv_def
                  by auto
                have len: "length (lin_data_in''_mv xs) + (idx_oldest_mv xs) = (idx_mid_mv xs)"
                  using mv_ln_eq
                  by auto
                then have IH_nonempty: "lin_data_in''_mv xs \<noteq> []"
                  using IH_nonempty
                  by auto
                then have not_relR: "as \<notin> snd (last (lin_data_in''_mv xs))"
                  using no_hist_last_not_sat[OF len tuple_since_tp]
                  by auto
                
                have "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some (get_idx_move tuple)"
                  using True mapping_eq
                  by (simp add: Mapping_lookup_upd_set)
                then have idx_eq: "idx = idx_mid_mv xs"
                  using IH(2) Some
                  unfolding tuple_def 
                  by auto
                moreover have idx_mid_eq: "idx_mid_mv xs + 1 = idx_mid_mv (xs @ [x])"
                  using mem
                  unfolding idx_mid_mv_def
                  by auto
                ultimately have idx_rel: "(idx - idx_oldest_mv (xs @ [x]) - 1) = (idx_mid_mv (xs @ [x]) - idx_oldest_mv (xs @ [x]) - 2)"
                  by auto
                moreover have "idx_mid_mv (xs @ [x]) - idx_oldest_mv (xs @ [x]) - 1 \<le> length (lin_data_in''_mv (xs))"
                proof -
                  have "length (lin_data_in''_mv xs) + (idx_oldest_mv (xs @ [x])) + 1 = idx_mid_mv (xs @ [x])"
                    using len idx_oldest_eq idx_mid_eq
                    by auto
                  then show ?thesis by auto
                qed
                ultimately have "lin_data_in''_mv (xs @ [x]) ! (idx - idx_oldest_mv (xs @ [x]) - 1) = lin_data_in''_mv (xs) ! (idx_mid_mv (xs @ [x]) - idx_oldest_mv (xs @ [x]) - 2)"
                  using data_in''_eq idx_append[of "idx_mid_mv (xs @ [x]) - idx_oldest_mv (xs @ [x]) - 2" "lin_data_in''_mv (xs)" "(\<lambda>(t, l, y). (t, y)) x"]
                  using idx_eq idx_oldest_eq assm len
                  by auto
                then have "lin_data_in''_mv (xs @ [x]) ! (idx - idx_oldest_mv (xs @ [x]) - 1) = lin_data_in''_mv (xs) ! (idx_mid_mv (xs) - idx_oldest_mv (xs) - 1)"
                  using idx_oldest_eq idx_mid_eq len idx_rel idx_eq
                  by auto
                moreover have "lin_data_in''_mv (xs) ! (idx_mid_mv (xs) - idx_oldest_mv (xs) - 1) = last (lin_data_in''_mv (xs))"
                  using len IH_nonempty
                  by (metis add_diff_cancel_right' last_conv_nth)
                ultimately show ?thesis using not_relR by auto
              next
                case not_mem: False
                then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup joined_mapping as"
                  using mapping_eq
                  by (metis Mapping_lookup_upd_set)
                then have relR: "as \<in> relR x"
                  unfolding joined_mapping_def
                  by (metis Mapping_lookup_filter_Some_P Some)
                then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup tuple_since_hist' as"
                  using Mapping_lookup_filter_not_None Some lookup_eq
                  unfolding joined_mapping_def
                  by fastforce
                then have lookup_eq: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Mapping.lookup (fst (fold fold_op_f xs init_tuple)) as"
                  unfolding tuple_since_hist'_def tuple_def
                  by auto
                then have "tuple_since_tp args as (lin_data_in''_mv xs) (idx_oldest_mv xs) (idx_mid_mv xs) idx"
                  using IH(1) IH_nonempty Some
                  unfolding tuple_since_hist_mv_def
                  by (auto split: option.splits)
                then have idx_props:
                  "idx < idx_mid_mv xs"
                  "idx > idx_oldest_mv xs \<longrightarrow> as \<notin> snd (lin_data_in''_mv xs ! (idx - idx_oldest_mv xs - 1))"
                  unfolding tuple_since_tp_def
                  by auto
                then have "as \<notin> snd (lin_data_in''_mv xs ! (idx - idx_oldest_mv (xs @ [x]) - 1))"
                  using assm idx_oldest_eq
                  by auto
                moreover have "idx - idx_oldest_mv (xs @ [x]) - 1 < length (lin_data_in''_mv xs)"
                  using assm idx_oldest_eq idx_props(1) mv_ln_eq less_diff_conv2
                  by auto
                ultimately show ?thesis
                  using idx_append[of "idx - idx_oldest_mv (xs @ [x]) - 1" "lin_data_in''_mv xs" "(\<lambda>(t, l, y). (t, y)) x"]
                        data_in''_eq
                  by auto
              qed
            qed
            ultimately have "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) idx"
              using data_in_nonempty
              unfolding tuple_since_tp_def
              by auto
            then show ?thesis using Some by auto
          qed
        qed
      qed
      moreover have hist_sat_props: "as \<in> (hist_sat_mv (xs @ [x]) init_tuple) =
        (((lin_data_in''_mv (xs @ [x])) \<noteq> []) \<and> (
          \<forall>(t, r) \<in> set (lin_data_in''_mv (xs @ [x])). as \<in> r
        ))"
      proof -
        have fold_eq: "(fst \<circ> snd) (fold fold_op_f (xs @ [x]) init_tuple) = (fst \<circ> snd) (fold_op_f x tuple)"
          using fold_alt[of fold_op_f xs x init_tuple]
          unfolding tuple_def
          by auto
        
        show "as \<in> (hist_sat_mv (xs @ [x]) init_tuple) =
        (((lin_data_in''_mv (xs @ [x])) \<noteq> []) \<and> (
          \<forall>(t, r) \<in> set (lin_data_in''_mv (xs @ [x])). as \<in> r
        ))"
        proof (cases "lin_data_in''_mv (xs @ [x]) = []")
          case True
          show ?thesis
          proof (rule iffI)
            assume "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
            then have "False" using True unfolding hist_sat_mv_def by auto
            then show "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
              by auto
          next
            assume "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
            then have "False" using True by auto
            then show "as \<in> hist_sat_mv (xs @ [x]) init_tuple" by auto
          qed
        next
          case non_empty: False
          show ?thesis
          proof (cases "lin_data_in''_mv xs = []")
            case True
            {
              assume "\<not>(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
              then have "(\<lambda>(t, _). \<not>memR (args_ivl args) (nt - t)) x" by auto
              then have "lin_data_in''_mv (xs @ [x]) = []"
                using True
                unfolding lin_data_in''_mv_def
                by auto
              then have "False" using non_empty by auto
            }
            then have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
              by blast
            then have lin_eq: "lin_data_in''_mv (xs @ [x]) = [(\<lambda>(t, l, r). (t, r)) x]"
              using True
              unfolding lin_data_in''_mv_def
              by auto

            show ?thesis
            proof (rule iffI)
              assume "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
              then have "as \<in> (((fst \<circ> snd) (fold fold_op_f xs init_tuple) \<inter> relR x) \<union> {as \<in> (snd o snd) x. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])})"
                using lin_eq fold_alt[of fold_op_f xs x init_tuple] fold_IH_hist_sat
                unfolding hist_sat_mv_def tuple_def hist_sat'_def
                by (auto split: list.splits simp add: case_prod_beta')
              moreover {
                assume "as \<in> ((fst \<circ> snd) (fold fold_op_f xs init_tuple) \<inter> relR x)"
                then have "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                  unfolding relR_def
                  by (auto simp add: case_prod_beta')
                then have "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                  using lin_eq
                  by auto
              }
              moreover {
                assume "as \<in> {as \<in> (snd o snd) x. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])}"
                then have "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                  by (auto simp add: case_prod_beta')
                then have "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                  using lin_eq
                  by auto
              }
              ultimately show "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                by auto
            next
              assume assm: "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
              then have tp: "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) (idx_oldest_mv (xs @ [x]))"
                using mv_ln_eq
                unfolding tuple_since_tp_def
                by (metis add_diff_cancel_right' in_set_dropD length_greater_0_conv less_irrefl zero_less_diff)
              have len: "length (lin_data_in''_mv (xs @ [x])) + idx_oldest_mv (xs @ [x]) = idx_mid_mv (xs @ [x])"
                using mv_ln_eq
                by auto
              obtain idx where "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some idx \<and> idx \<le> idx_oldest_mv (xs @ [x])"
                using tuple_since_hist_lookup_leq[OF tuple_since_hist_mv_props tp len]
                by auto
              moreover have relR: "as \<in> relR x"
                using assm lin_eq
                unfolding relR_def
                by (auto simp add: case_prod_beta')
              ultimately have "as \<in> {as \<in> (snd o snd) x. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])}"
                unfolding relR_def
                by auto
              then show "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
                using lin_eq relR
                unfolding hist_sat_mv_def relR_def
                by (auto split: list.splits simp add: case_prod_beta')
            qed
          next
            case False
            show ?thesis
            proof (rule iffI)
              assume assm: "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
              then obtain db dbs where db_props: "db#dbs = lin_data_in''_mv (xs @ [x])"
                unfolding hist_sat_mv_def
                by (auto split: list.splits)
              then have "as \<in> ((fst \<circ> snd) (fold_op_f x tuple) \<union> {as \<in> snd db. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])})"
                using assm fold_eq
                unfolding hist_sat_mv_def
                by (auto split: list.splits)
              moreover {
                assume as_mem: "as \<in> (fst \<circ> snd) (fold_op_f x tuple)"
                then have as_props:
                    "as \<in> hist_sat'"
                    "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                  using fold_IH_hist_sat
                  unfolding relR_def
                  by (auto simp add: case_prod_beta')
                moreover have "(\<forall>(t, r)\<in>set (lin_data_in''_mv xs). as \<in> r)"
                  using as_props(1) IH(4) False
                  unfolding hist_sat_mv_def hist_sat'_def tuple_def
                  by (auto split: list.splits)
                ultimately have "\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r"
                  unfolding lin_data_in''_mv_def
                  by auto
              }
              moreover {
                assume "as \<in> {as \<in> snd db. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])}"
                then obtain idx where idx_props: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some idx" "idx \<le> idx_oldest_mv (xs @ [x])"
                  by (auto split: option.splits)
                then have "\<forall>(t, y)\<in>set (drop (idx - idx_oldest_mv (xs @ [x])) (lin_data_in''_mv (xs @ [x]))). as \<in> y"
                  using tuple_since_hist_mv_props
                  unfolding tuple_since_tp_def
                  by auto
                then have "\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r"
                  using idx_props(2)
                  by auto
              }
              ultimately have "\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r" by auto
  
              then show "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                using db_props
                by auto
            next
              assume assm: "lin_data_in''_mv (xs @ [x]) \<noteq> [] \<and> (\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
              then have tp: "tuple_since_tp args as (lin_data_in''_mv (xs @ [x])) (idx_oldest_mv (xs @ [x])) (idx_mid_mv (xs @ [x])) (idx_oldest_mv (xs @ [x]))"
                using mv_ln_eq
                unfolding tuple_since_tp_def
                by (metis add_diff_cancel_right' in_set_dropD length_greater_0_conv less_irrefl zero_less_diff)
              have len: "length (lin_data_in''_mv (xs @ [x])) + idx_oldest_mv (xs @ [x]) = idx_mid_mv (xs @ [x])"
                using mv_ln_eq
                by auto
              obtain idx where idx_props: "Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as = Some idx \<and> idx \<le> idx_oldest_mv (xs @ [x])"
                using tuple_since_hist_lookup_leq[OF tuple_since_hist_mv_props tp len]
                by auto
              then have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
                using mem non_empty snoc(2)
                by auto
              then have relR: "as \<in> relR x"
                using assm
                unfolding relR_def lin_data_in''_mv_def
                by (auto simp add: case_prod_beta')
              then have "as \<in> {as \<in> (snd o snd) x. case Mapping.lookup (tuple_since_hist_mv (xs @ [x]) init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv (xs @ [x])}"
                using idx_props
                unfolding relR_def
                by auto
              then show "as \<in> hist_sat_mv (xs @ [x]) init_tuple"
                using assm
                unfolding hist_sat_mv_def
                by (auto split: list.splits simp add: case_prod_beta')
            qed
          qed
        qed
      qed
      (* fold_IH_since_sat *)
      moreover have "(as \<in> since_sat_mv (xs @ [x]) init_tuple \<longrightarrow> as \<in> hist_sat_mv (xs @ [x]) init_tuple \<or> tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args maskL (lin_data_in''_aux_mv (xs @ [x])))"
      proof -
        {
          assume assm: "as \<in> since_sat_mv (xs @ [x]) init_tuple"
          then have non_empty: "lin_data_in''_mv (xs @ [x]) \<noteq> []"
            using mv_ln_eq
            unfolding since_sat_mv_def
            by (metis comm_monoid_add_class.add_0 equals0D length_nth_simps(1))
          then have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
            using mem
            by auto

          have "as \<in> (snd \<circ> snd \<circ> snd) (fold fold_op_f (xs @ [x]) init_tuple)"
            using assm
            unfolding since_sat_mv_def
            by (auto split: if_splits)

          then have "as \<in> (snd \<circ> snd \<circ> snd) (fold_op_f x (fold fold_op_f xs init_tuple))"
            using fold_alt[of fold_op_f xs x init_tuple]
            by auto
          then have as_mem: "as \<in> (since_sat' \<inter> relR x) \<union> {as \<in> relR x. proj_tuple_in_join (args_pos args) maskL as (relL x)}"
            using fold_IH_since_sat
            unfolding tuple_def
            by auto

          have " as \<in> hist_sat_mv (xs @ [x]) init_tuple \<or> tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args maskL (lin_data_in''_aux_mv (xs @ [x]))"
          proof (cases "as \<in> (since_sat' \<inter> relR x)")
            case True
            then have relR: "as \<in> relR x" by auto
            then show ?thesis
            proof (cases "lin_data_in''_mv xs = []")
              case empty: True
              then have "lin_data_in''_mv (xs @ [x]) = [(\<lambda>(t, l, r). (t, r)) x]"
                using mem
                unfolding lin_data_in''_mv_def
                by auto
              moreover have "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                using relR
                unfolding relR_def
                by (simp add: case_prod_beta)
              ultimately have "(\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r)"
                by auto
              then have "as \<in> (hist_sat_mv (xs @ [x]) init_tuple)"
                using non_empty hist_sat_props
                by auto
              then show ?thesis by auto
            next
              case IH_nonempty: False
              then have "idx_mid_mv xs \<noteq> idx_oldest_mv xs"
                using mv_ln_eq
                by (metis add_cancel_left_left length_0_conv)
              then have "as \<in> hist_sat_mv xs init_tuple \<or> tuple_since_lhs as (lin_data_in''_mv xs) args maskL (lin_data_in''_aux_mv xs)"
                using True IH(5) IH_nonempty
                unfolding since_sat'_def tuple_def since_sat_mv_def
                by (auto split: if_splits)
              moreover {
                assume "as \<in> hist_sat_mv xs init_tuple"
                then have "\<forall>(t, r)\<in>set (lin_data_in''_mv xs). as \<in> r"
                  using IH(4)
                  by auto
                moreover have "lin_data_in''_mv (xs @ [x]) = lin_data_in''_mv xs @ [(\<lambda>(t, l, r). (t, r)) x]"
                  using mem
                  unfolding lin_data_in''_mv_def
                  by auto
                moreover have "as \<in> snd ((\<lambda>(t, l, r). (t, r)) x)"
                  using relR
                  unfolding relR_def
                  by (simp add: case_prod_beta)
                ultimately have "\<forall>(t, r)\<in>set (lin_data_in''_mv (xs @ [x])). as \<in> r"
                  by auto
                then have "as \<in> (hist_sat_mv (xs @ [x]) init_tuple)"
                  using non_empty hist_sat_props
                  by auto
                then have ?thesis by auto
              }
              moreover {
                assume "tuple_since_lhs as (lin_data_in''_mv xs) args maskL (lin_data_in''_aux_mv xs)"
                then obtain n where n_props:
                  "n\<in>{0..<length (lin_data_in''_mv xs)}"
                  "\<forall>(t, l, y)\<in>set (drop n (lin_data_in''_aux_mv xs)). as \<in> y"
                  "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv xs)))) (proj_tuple maskL as)"
                  unfolding tuple_since_lhs_def
                  by (auto simp add: Let_def)
                have n_l: "n < length (lin_data_in''_aux_mv xs)"
                  using n_props(1) data_in''_aux_eq
                  by (metis atLeastLessThan_iff length_map)
                then have drop_eq: "drop n (lin_data_in''_aux_mv (xs @ [x])) = drop n (lin_data_in''_aux_mv xs) @ [x]"
                  using mem
                  unfolding lin_data_in''_aux_mv_def
                  by auto
                then have all_relR: "\<forall>(t, l, y)\<in>set (drop n (lin_data_in''_aux_mv (xs @ [x]))). as \<in> y"
                  using n_props(2) relR
                  unfolding lin_data_in''_aux_mv_def relR_def
                  by auto

                have "hd (drop n (lin_data_in''_aux_mv xs)) = hd (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                  using n_l drop_eq hd_append[of "drop n (lin_data_in''_aux_mv xs)" "[x]"]
                  by auto
                then have "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv (xs @ [x]))))) (proj_tuple maskL as)"
                  using n_props(3)
                  by auto
                then have "let suffix = drop n (lin_data_in''_aux_mv (xs @ [x])) in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL as)"
                  using non_empty all_relR
                  by auto
                moreover have "n\<in>{0..<length (lin_data_in''_mv (xs @ [x]))}"
                  using n_props(1)
                  unfolding lin_data_in''_mv_def
                  by auto
                ultimately have "tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args maskL (lin_data_in''_aux_mv (xs @ [x]))"
                  using non_empty
                  unfolding tuple_since_lhs_def
                  by blast
                then have ?thesis by auto
              }
              ultimately show ?thesis by blast
            qed
          next
            case False
            then have as_mem: "as \<in> {as \<in> relR x. proj_tuple_in_join (args_pos args) maskL as (relL x)}"
              using as_mem
              by auto
            then have
              "as \<in> relR x"
              "proj_tuple_in_join (args_pos args) maskL as (relL x)"
              by auto
            then have x_props:
              "as \<in> relR x"
              "join_cond (args_pos args) (relL x) (proj_tuple maskL as)"
              unfolding proj_tuple_in_join_def
              by auto
            define n where "n = length (lin_data_in''_aux_mv (xs @ [x])) - 1"
            then have drop_eq: "drop n (lin_data_in''_aux_mv (xs @ [x])) = [x]"
              using mem
              unfolding lin_data_in''_aux_mv_def
              by auto
            then have "\<forall>(t, l, y)\<in>set (drop n (lin_data_in''_aux_mv (xs @ [x]))). as \<in> y"
              using x_props(1)
              unfolding relR_def
              by auto
            moreover have "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv (xs @ [x]))))) (proj_tuple maskL as)"
              using drop_eq x_props(2)
              by auto
            ultimately have "(let suffix = drop n (lin_data_in''_aux_mv (xs @ [x])) in
              (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and>
              join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL as)
            )"
              by auto
            moreover have "n\<in>{0..<length (lin_data_in''_mv (xs @ [x]))}"
              using n_def non_empty data_in''_aux_eq
              by (metis (no_types, lifting) One_nat_def atLeastLessThan_iff diff_Suc_less length_greater_0_conv length_map zero_le)
            ultimately have "tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args maskL (lin_data_in''_aux_mv (xs @ [x]))"
              using non_empty
              unfolding tuple_since_lhs_def
              by blast
            then show ?thesis by auto
          qed
        }
        then show ?thesis by auto
      qed
      moreover have "(tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args maskL (lin_data_in''_aux_mv (xs @ [x])) \<longrightarrow> as \<in> since_sat_mv (xs @ [x]) init_tuple)"
      proof -
        {
          assume assm: "tuple_since_lhs as (lin_data_in''_mv (xs @ [x])) args maskL (lin_data_in''_aux_mv (xs @ [x]))"
          then have non_empty: "lin_data_in''_mv (xs @ [x]) \<noteq> []"
            unfolding tuple_since_lhs_def
            by auto
          then have mem: "(\<lambda>(t, _). memR (args_ivl args) (nt - t)) x"
            using mem
            by auto
          obtain n where n_props:
            "n\<in>{0..<length (lin_data_in''_mv (xs @ [x]))}"
            "(\<forall>(t, l, r)\<in>set (drop n (lin_data_in''_aux_mv (xs @ [x]))). as \<in> r)"
            "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv (xs @ [x]))))) (proj_tuple maskL as)"
            using assm 
            unfolding tuple_since_lhs_def
            by (auto simp add: Let_def)
          
          have "as \<in> (since_sat' \<inter> relR x) \<union> {as \<in> relR x. proj_tuple_in_join (args_pos args) maskL as (relL x)}"
          proof (cases "lin_data_in''_mv xs = []")
            case True
            then have lin_data_in''_eq: "lin_data_in''_mv (xs @ [x]) = [(\<lambda>(t, l, r). (t, r)) x]"
              using mem
              unfolding lin_data_in''_mv_def
              by auto
            then have "lin_data_in''_aux_mv (xs @ [x]) = [x]"
              using True data_in''_aux_eq data_in'_aux_eq mem
              unfolding lin_data_in''_aux_mv_def lin_data_in''_mv_def
              by auto
            then have
              "as \<in> relR x"
              "join_cond (args_pos args) (relL x) (proj_tuple maskL as)"
              using n_props lin_data_in''_eq
              unfolding relR_def
              by auto
            then have "as \<in> {as \<in> relR x. proj_tuple_in_join (args_pos args) maskL as (relL x)}"
              unfolding proj_tuple_in_join_def
              by auto
            then show ?thesis by auto
          next
            case False
            
            {
              assume n_l: "n\<in>{0..<length (lin_data_in''_mv xs)}"
              {
                fix t l r
                assume "(t, l, r)\<in>set (drop n (lin_data_in''_aux_mv (xs)))"
                then have "(t, l, r)\<in>set (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                  unfolding lin_data_in''_aux_mv_def
                  by auto
              }
              then have relR:
                "(\<forall>(t, l, r)\<in>set (drop n (lin_data_in''_aux_mv (xs))). as \<in> r)"
                using n_props(2)
                by blast

              have "hd (drop n (lin_data_in''_aux_mv (xs @ [x]))) = hd (drop n ((data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) [x]))"
                unfolding lin_data_in''_aux_mv_def
                by auto
              moreover have "length (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) \<ge> n"
                using n_l data_in'_aux_eq
                unfolding lin_data_in''_mv_def
                by (metis atLeastLessThan_iff data_in''_aux_eq length_map less_imp_le_nat lin_data_in''_aux_mv_def n_l)
              ultimately have "hd (drop n (lin_data_in''_aux_mv (xs @ [x]))) = hd (drop n (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) [x])"
                using n_l drop_append[of n "(data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs)" "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) [x]"]
                by auto
              moreover have "drop n (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs) \<noteq> []"
                using False data_in''_aux_eq n_l
                unfolding lin_data_in''_aux_mv_def lin_data_in''_mv_def
                by (metis (no_types, lifting) atLeastLessThan_iff length_drop length_map length_nth_simps(1) not_less0 zero_less_diff)
              ultimately have "hd (drop n (lin_data_in''_aux_mv (xs @ [x]))) = hd (drop n (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs))"
                using hd_append[of "drop n (data_in'_aux @ filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) xs)" "filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) [x]"]
                by auto
              then have "hd (drop n (lin_data_in''_aux_mv xs)) = hd (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                unfolding lin_data_in''_aux_mv_def
                by auto
              then have "join_cond (args_pos args) (relL (hd (drop n (lin_data_in''_aux_mv xs)))) (proj_tuple maskL as)"
                using n_props(3)
                by auto

              then have "(let suffix = drop n (lin_data_in''_aux_mv xs) in (\<forall>(t, l, y)\<in>set suffix. as \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL as))"
                using relR
                by auto
              then have "tuple_since_lhs as (lin_data_in''_mv xs) args maskL (lin_data_in''_aux_mv xs)"
                using n_l False
                unfolding tuple_since_lhs_def
                by blast
              then have "as \<in> (snd \<circ> snd \<circ> snd) (fold fold_op_f xs init_tuple)"
                using IH(6) mv_ln_eq False
                unfolding since_sat_mv_def
                by (meson equals0D)
              then have "as \<in> since_sat'"
                unfolding since_sat'_def tuple_def
                by auto
              moreover have "as \<in> relR x"
              proof -
                have "n < length (lin_data_in''_aux_mv (xs @ [x]))"
                  using n_props(1) data_in'_aux_eq
                  unfolding lin_data_in''_aux_mv_def lin_data_in''_mv_def
                  using length_map[of "\<lambda>(t, l, y). (t, y)" "(filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (xs @ [x]))"]
                  (* generated subproof *)
                  proof -
                    show "n < length (data_in'_aux @ filter (\<lambda>(n, p). memR (args_ivl args) (nt - n)) (xs @ [x]))"
                      by (metis atLeastLessThan_iff data_in''_aux_eq length_map lin_data_in''_aux_mv_def n_props(1))
                  qed
                then have "x \<in> set (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                  using mem
                  unfolding lin_data_in''_aux_mv_def
                  by auto
                then show ?thesis using n_props(2) unfolding relR_def by auto
              qed
              ultimately have "as \<in> (since_sat' \<inter> relR x) \<union> {as \<in> relR x. proj_tuple_in_join (args_pos args) maskL as (relL x)}"
                by auto
            }
            moreover {
              assume "n \<notin> {0..<length (lin_data_in''_mv xs)}"
              then have "n\<in>{length (lin_data_in''_mv xs)..<length (lin_data_in''_mv (xs @ [x]))}"
                using n_props(1)
                by auto
              moreover have "length (lin_data_in''_mv (xs @ [x])) = length (lin_data_in''_mv (xs)) + 1"
                using mem
                unfolding lin_data_in''_mv_def
                by auto
              ultimately have "n = length (lin_data_in''_mv xs)"
                by auto
              then have n_eq: "n = length (lin_data_in''_aux_mv xs)"
                using data_in''_aux_eq
                by (metis length_map)
              then have
                "(hd (drop n (lin_data_in''_aux_mv (xs @ [x])))) = x"
                "x \<in> set (drop n (lin_data_in''_aux_mv (xs @ [x])))"
                using mem
                unfolding lin_data_in''_aux_mv_def
                by auto
              then have
                "as \<in> relR x"
                "join_cond (args_pos args) (relL x) (proj_tuple maskL as)"
                using n_props(2-3)
                unfolding relR_def
                by auto
              then have "as \<in> {as \<in> relR x. proj_tuple_in_join (args_pos args) maskL as (relL x)}"
                unfolding proj_tuple_in_join_def
                by auto
            }
            ultimately show ?thesis by blast
          qed
          then have "as \<in> (snd \<circ> snd \<circ> snd) (fold_op_f x (fold fold_op_f xs init_tuple))"
            using fold_IH_since_sat
            unfolding tuple_def
            by auto
          then have "as \<in> (snd \<circ> snd \<circ> snd) (fold fold_op_f (xs @ [x]) init_tuple)"
            using fold_alt[of fold_op_f xs x init_tuple]
            by auto
          then have "as \<in> since_sat_mv (xs @ [x]) init_tuple"
            using mv_ln_eq non_empty
            unfolding since_sat_mv_def since_sat'_def tuple_def
            by (metis add_cancel_left_left length_0_conv)
        }
        then show ?thesis by auto
      qed
      moreover have "get_idx_move (fold fold_op_f (xs @ [x]) init_tuple) = idx_mid_mv (xs @ [x])"
      proof -
        have "fold fold_op_f (xs @ [x]) init_tuple = fold_op_f x tuple"
          using fold_alt[of fold_op_f "xs" "x" init_tuple]
          unfolding tuple_def
          by auto
        moreover have "get_idx_move (fold_op_f x tuple) = (get_idx_move tuple) + 1"
          unfolding get_idx_move_def fold_op_f_def
          by (smt case_prod_beta' comp_apply fst_conv prod.sel(2))
        moreover have "(get_idx_move tuple) + 1 = idx_mid_mv (xs @ [x])"
          using IH(2)
          unfolding tuple_def idx_mid_mv_def
          by auto
        ultimately show ?thesis by auto
      qed
      moreover have "(case Mapping.lookup (fst (fold fold_op_f (xs @ [x]) init_tuple)) as of None \<Rightarrow> True | Some idx \<Rightarrow> idx < idx_mid_mv (xs @ [x]))"
      proof -
        have "fold fold_op_f (xs @ [x]) init_tuple = fold_op_f x (fold fold_op_f xs init_tuple)"
          using fold_alt[of fold_op_f xs x init_tuple]
          by auto
        then have mapping_eq: "fst (fold fold_op_f (xs @ [x]) init_tuple) = upd_set joined_mapping (\<lambda>_. get_idx_move tuple) (relR x - Mapping.keys joined_mapping)"
          using fold_IH_since_hist
          unfolding tuple_def
          by auto
        show ?thesis
        proof (cases "Mapping.lookup (fst (fold fold_op_f (xs @ [x]) init_tuple)) as")
          case (Some idx)
          then show ?thesis
          proof (cases "as \<in> (relR x - Mapping.keys joined_mapping)")
            case True
            then have "idx = get_idx_move tuple"
              using Some mapping_eq
              by (simp add: Mapping_lookup_upd_set)
            then show ?thesis
              using IH(2-3) Some
              unfolding tuple_def idx_mid_mv_def
              by auto
          next
            case False
            then have "Mapping.lookup (fst (fold fold_op_f (xs @ [x]) init_tuple)) as = Mapping.lookup joined_mapping as"
              using mapping_eq
              by (metis Mapping_lookup_upd_set)
            then have "Mapping.lookup (fst (fold fold_op_f (xs @ [x]) init_tuple)) as = Mapping.lookup tuple_since_hist' as"
              unfolding joined_mapping_def
              using Some Mapping_lookup_filter_not_None
              by fastforce
            then show ?thesis
              unfolding tuple_since_hist'_def tuple_def
              using IH(3) Some idx_mid_mv_def
              by auto
          qed
        qed (auto)
      qed
      ultimately show ?case by auto
    qed
    moreover have is_empty_eq: "(idx_mid_mv move = idx_oldest_mv move) = is_empty data_in''"
      using mv_idx_mid' mv_idx_oldest' data_in''_len' is_empty_alt[of data_in'']
      by auto
    moreover have since_hist''_eq: "tuple_since_hist_mv move init_tuple = tuple_since_hist''"
      using is_empty_eq fold_tuple_res
      unfolding tuple_since_hist''_def tuple_since_hist_mv_def init_tuple_def
      by (metis fst_conv)
    moreover have "hist_sat_mv move init_tuple = hist_sat''"
    proof -
      have hist_sat'_eq: "(fst \<circ> snd) (fold fold_op_f move init_tuple) = hist_sat'"
        using fold_tuple_res
        unfolding init_tuple_def
        by (metis comp_apply fst_conv snd_conv)
      {
        fix x
        assume assm: "x \<in> hist_sat_mv move init_tuple"
        then obtain db dbs where db_props: "db#dbs = linearize data_in''"
          unfolding hist_sat_mv_def mv_data_in''
          by (auto split: list.splits)
        then have lin_non_empty: "linearize (data_in'') \<noteq> []"
          by auto
        then have non_empty: "\<not> is_empty (data_in'')"
          using is_empty_alt
          by auto

        have hd_in: "hd (linearize data_in'') = db"
          using db_props mv_data_in''
          by (metis list.sel(1))

        obtain dbs' where safe_hd_eq: "safe_hd data_in'' = (Some db, dbs')"
          using safe_hd_rep[of data_in''] db_props
          by (smt lin_non_empty case_optionE hd_in safe_hd_rep surjective_pairing)
        
        have "x \<in> (fst \<circ> snd) (fold fold_op_f move init_tuple) \<union> {as \<in> snd db. case Mapping.lookup tuple_since_hist'' as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest'}"
          using db_props assm since_hist''_eq mv_idx_oldest' mv_data_in''
          unfolding hist_sat_mv_def
          by (auto split: list.splits)
        then have "x \<in> hist_sat' \<union> {as \<in> snd db. case Mapping.lookup tuple_since_hist'' as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest'}"
          using hist_sat'_eq
          by auto
        moreover have "fst (safe_hd data_in'') = Some db"
          using safe_hd_eq
          by auto
        ultimately have "x \<in> hist_sat''"
          using hist_sat''_def
          by auto
      }
      moreover {
        fix x
        assume assm: "x \<in> hist_sat''"
        then obtain db dbs' where safe_hd_eq:
          "safe_hd data_in'' = (Some db, dbs')"
          unfolding hist_sat''_def
          by (smt empty_iff eq_fst_iff option.exhaust option.simps(4))
        then have x_mem: "x \<in> hist_sat' \<union> {tuple \<in> snd db. case Mapping.lookup tuple_since_hist'' tuple of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest'}"
          using assm
          unfolding hist_sat''_def
          by auto
        have hd_props:
          "linearize data_in'' \<noteq> []"
          "db = hd (linearize data_in'')"
          using safe_hd_eq safe_hd_rep[of data_in'' "Some db" dbs']
          by auto
        then obtain dbs where dbs_props: "linearize data_in'' = db#dbs"
          by (metis hd_Cons_tl)
        have "x \<in> (fst \<circ> snd) (fold fold_op_f move init_tuple) \<union> {as \<in> snd db. case Mapping.lookup (tuple_since_hist_mv move init_tuple) as of None \<Rightarrow> False | Some idx \<Rightarrow> idx \<le> idx_oldest_mv move}"
          using x_mem mv_data_in''
          unfolding mv_idx_oldest' since_hist''_eq[symmetric] hist_sat'_eq
          by auto
        then have "x \<in> hist_sat_mv move init_tuple"
          using mv_data_in'' hd_props(1) dbs_props
          unfolding hist_sat_mv_def
          by (auto split: list.splits)
      }
      ultimately show ?thesis by auto
    qed
    moreover have "since_sat_mv move init_tuple = since_sat''"
      using fold_tuple_res
      unfolding since_sat''_def since_sat_mv_def mv_idx_oldest'[symmetric] mv_idx_mid'[symmetric]
                init_tuple_def
      apply (auto split: if_splits)
      by (metis (full_types) snd_conv)+
    moreover have "(lin_data_in''_aux_mv move) = (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist))"
    proof -

      have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> mem (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t))) = (\<lambda>(t, _). mem (args_ivl args) (mt - t))"
        using nt_mono(1) time not_memL_nt_mt
        by blast

      have filter_simp': "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). mem (args_ivl args) (nt - t))"
        by auto

      have "(lin_data_in''_aux_mv move) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) ((auxlist_data_in args mt auxlist) @ filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
        using auxlist_eqs(2) filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))"]
        unfolding lin_data_in''_aux_mv_def data_in'_aux_def move_filter
        by auto
      moreover have "(auxlist_data_in args mt auxlist) = filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist)"
        unfolding auxlist_data_in_def
        using filter_filter[of "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(\<lambda>(t, _). mem (args_ivl args) (mt - t))" auxlist]
        by (auto simp add: filter_simp)
      moreover have "auxlist_data_prev args mt auxlist = linearize data_prev"
        using assms(1)
        by auto
      ultimately have "(lin_data_in''_aux_mv move) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (auxlist_data_in args mt auxlist @ auxlist_data_prev args mt auxlist))"
        by auto
      then have "(lin_data_in''_aux_mv move) = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) auxlist)"
        using auxlist_eqs
        by auto
      then have "(lin_data_in''_aux_mv move) = (auxlist_data_in args nt auxlist)"
        using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" auxlist]
        unfolding auxlist_data_in_def
        by (auto simp add: filter_simp')
      then show ?thesis using data_in_auxlist_filter_eq by auto
    qed
    ultimately have "(case Mapping.lookup (tuple_since_hist'') as of
      None \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)"
       "(as \<in> hist_sat'') = (linearize data_in'' \<noteq> [] \<and> (\<forall>(t, r)\<in>set (linearize data_in''). as \<in> r))"
       "(as \<in> since_sat'' \<longrightarrow> as \<in> hist_sat'' \<or> tuple_since_lhs as (linearize data_in'') args maskL (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)))"
       "(tuple_since_lhs as (linearize data_in'') args maskL (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) \<longrightarrow> as \<in> since_sat'')"
      by (auto simp add: mv_data_in''[symmetric] mv_idx_oldest'[symmetric] mv_idx_mid'[symmetric] split: option.splits)
  }
  then have fold_induct_props: "\<forall>as. (case Mapping.lookup (tuple_since_hist'') as of
      None \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)"
       "\<forall>as. (as \<in> hist_sat'') = (linearize data_in'' \<noteq> [] \<and> (\<forall>(t, r)\<in>set (linearize data_in''). as \<in> r))"
       "\<forall>as. (as \<in> since_sat'' \<longrightarrow> as \<in> hist_sat'' \<or> tuple_since_lhs as (linearize data_in'') args maskL (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)))"
       "\<forall>as. (tuple_since_lhs as (linearize data_in'') args maskL (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist)) \<longrightarrow> as \<in> since_sat'')"
    by auto

  show tuple_since_hist''_props: "\<forall>as. (case Mapping.lookup (tuple_since_hist'') as of
      None \<Rightarrow> \<forall>idx. \<not> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)"
    using fold_induct_props(1)
    by auto
  
  have "\<forall>as \<in> Mapping.keys (tuple_since_hist''). wf_tuple (args_n args) (args_R args) as"
  proof -
    {
      fix as
      assume "as \<in> Mapping.keys (tuple_since_hist'')"
      then obtain idx where "Mapping.lookup tuple_since_hist'' as = Some idx"
        by (meson Mapping_keys_dest)
      then have idx_props:
        "linearize data_in'' \<noteq> []"
        "idx < idx_mid'"
        "\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in'')). as \<in> y"
        using tuple_since_hist''_props
        unfolding tuple_since_tp_def
        by (auto split: option.splits)
      then have "idx - idx_oldest' < length (linearize data_in'')"
        using data_in''_len'
        by (metis add.commute add_diff_cancel_left' diff_is_0_eq diff_less_mono not_le_imp_less length_0_conv less_imp_le_nat)
      then have "last (linearize data_in'') \<in> set (drop (idx - idx_oldest') (linearize data_in''))"
        using idx_props(1)
        by (metis drop_eq_Nil last_drop last_in_set leD)
      then have as_in: "as \<in> snd (last (linearize data_in''))"
        using idx_props(3)
        by auto
      then obtain t r where t_r_def: "(t, r) = last (linearize data_in'')"
        using prod.collapse
        by blast
      then have "(t, r) \<in> set (linearize data_in'')"
        by (metis idx_props(1) last_in_set)
      then obtain l where "(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) auxlist))"
        using auxlist_data_in
        by (smt case_prod_beta' fst_conv imageE prod.collapse set_map snd_conv)
      then have "(t, l, r) \<in> set auxlist"
        unfolding auxlist_data_in_def
        by auto
      moreover have "(\<forall>(t, relL, relR) \<in> set auxlist. table (args_n args) (args_L args) relL \<and> table (args_n args) (args_R args) relR)"
        using assms(1)
        by auto
      ultimately have "table (args_n args) (args_R args) r" by auto
      then have "wf_tuple (args_n args) (args_R args) as"
        using as_in t_r_def
        unfolding table_def
        by (metis snd_conv)
    }
    then show ?thesis by auto
  qed
  then show "table (args_n args) (args_R args) (Mapping.keys tuple_since_hist'')"
    unfolding table_def
    by auto

  
  show "(\<forall>tuple. tuple \<in> hist_sat'' \<longleftrightarrow>
      (\<not>is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r
    ))"
  proof -
    {
      fix tuple
      have "tuple \<in> hist_sat'' \<longleftrightarrow>
      (\<not>is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r)"
      proof (rule iffI)
        assume "tuple \<in> hist_sat''"
        then have props:
          "(\<not>is_empty data_in'')"
          "\<forall>(t, r)\<in>set (linearize data_in''). tuple \<in> r"
          using fold_induct_props(2) is_empty_alt
          by auto
        {
          fix t l r
          assume "(t, l, r) \<in> set (auxlist_data_in args nt auxlist)"
          then have "(t, r) \<in> set (linearize data_in'')"
            unfolding auxlist_data_in[symmetric] data_in_auxlist_filter_eq
            using set_map[of "(\<lambda>(t, l, y). (t, y))" "auxlist_data_in args nt auxlist"]
            by force
          then have "tuple \<in> r"
            using props(2)
            by auto
        }
        then show "(\<not>is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r)"
          using data_in_auxlist_filter_eq props(1)
          by auto
      next
        assume assm: "(\<not>is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)). tuple \<in> r)"
        then have "\<forall>(t, r) \<in> set (linearize data_in''). tuple \<in> r"
          using auxlist_data_in data_in_auxlist_filter_eq[symmetric] set_map[of "(\<lambda>(t, l, y). (t, y))" "auxlist_data_in args nt auxlist"]
          by auto
        then show "tuple \<in> hist_sat''"
          using assm fold_induct_props(2) is_empty_alt
          by auto
      qed
    }
    then show ?thesis by auto
  qed

  show "(\<forall>tuple. tuple \<in> since_sat'' \<longrightarrow>
      ((tuple \<in> hist_sat'') \<or> tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)))
    )"
    using fold_induct_props(3)
    by auto

  show "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)) \<longrightarrow>
      tuple \<in> since_sat''
    )"
    using fold_induct_props(4)
    by auto
  
qed

lemma valid_update_mmtaux':
  assumes valid_before: "valid_mmtaux args cur
    (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes nt_mono: "nt \<ge> cur"
  assumes "(idx_mid', idx_oldest', data_prev', data_in'', tuple_in_once', tuple_in_once_keys', tuple_since_hist'', hist_sat'', since_sat'') = update_mmtaux' args nt idx_mid idx_oldest maskL maskR data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat"
  shows "valid_mmtaux args nt
    (nt, idx_next, idx_mid', idx_oldest', maskL, maskR, data_prev', data_in'', tuple_in_once', tuple_in_once_keys', tuple_since_hist'', hist_sat'', since_sat'') (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  define auxlist' where "auxlist' = filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist"
  have "(if mem (args_ivl args) 0 then (args_L args) \<subseteq> (args_R args) else (args_L args) = (args_R args))"
    using assms(1)
    by auto
  moreover have "\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args"
    using assms(1)
    by auto
  moreover have "maskL = join_mask (args_n args) (args_L args)"
    using assms(1)
    by auto
  moreover have "maskR = join_mask (args_n args) (args_R args)"
    using assms(1)
    by auto
  moreover have "(\<forall>(t, relL, relR) \<in> set auxlist'. table (args_n args) (args_L args) relL \<and> table (args_n args) (args_R args) relR)"
    using assms(1)
    unfolding auxlist'_def
    by auto
  moreover have "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "table (args_n args) (args_R args) (Mapping.keys tuple_since_hist'')"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_L args) as)"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as)"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in''))). wf_tuple (args_n args) (args_R args) as)"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist')) =
    ts_tuple_rel (set (linearize data_in''))"
    using valid_update_mmtaux'_unfolded[OF assms]
    unfolding auxlist'_def
    by auto
  moreover have "sorted (map fst auxlist')"
    using assms(1) sorted_filter
    unfolding auxlist'_def
    by auto
  moreover have "auxlist_data_prev args nt auxlist' = (linearize data_prev')"
    using valid_update_mmtaux'_unfolded[OF assms]
    unfolding auxlist'_def
    by auto
  moreover have "auxlist_data_prev args nt auxlist' = drop (length (linearize data_in'')) auxlist'"
    using valid_update_mmtaux'_unfolded[OF assms]
    unfolding auxlist'_def
    by auto
  moreover have "length (linearize data_prev') + idx_mid' = idx_next"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in'')"
    using valid_update_mmtaux'_unfolded[OF assms]
    unfolding auxlist'_def
    by auto
  moreover have "auxlist_data_in args nt auxlist' = take (length (linearize data_in'')) auxlist'"
    using valid_update_mmtaux'_unfolded[OF assms]
    unfolding auxlist'_def
    by auto
  moreover have "length (linearize data_in'') + idx_oldest' = idx_mid'"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "(\<forall>db \<in> set auxlist'. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
  proof -
    {
      fix db
      assume assm: "db \<in> set auxlist'"

      have "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db))"
        using assms(1)
        by auto
      moreover have "db \<in> set auxlist"
        using assm
        unfolding auxlist'_def
        by auto
      ultimately have "time db \<le> mt"
        by auto
      then have "time db \<le> nt"
        using nt_mono assms(1)
        by auto

      moreover have "memR (args_ivl args) (nt - time db)"
        using assm
        unfolding auxlist'_def time_def
        by auto

      ultimately have "time db \<le> nt \<and> memR (args_ivl args) (nt - time db)"
        by auto
    }
    then show ?thesis by auto
  qed
  moreover have "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l (proj_tuple maskL as)) \<and>
    (\<forall>as. (case Mapping.lookup tuple_since_hist'' as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid' idx)
    )"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  moreover have "(\<forall>tuple. tuple \<in> hist_sat'' \<longleftrightarrow>
      (\<not>is_empty data_in'') \<and> (
        \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r
    ))"
    using valid_update_mmtaux'_unfolded[OF assms]
    unfolding auxlist'_def
    by auto
  moreover have "(\<forall>tuple. tuple \<in> since_sat'' \<longrightarrow>
      ((tuple \<in> hist_sat'') \<or> tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist'))
    )"
    using valid_update_mmtaux'_unfolded[OF assms]
    unfolding auxlist'_def
    by auto
  moreover have "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist') \<longrightarrow>
      tuple \<in> since_sat''
    )"
    using valid_update_mmtaux'_unfolded[OF assms]
    unfolding auxlist'_def
    by auto
  moreover have "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
    using valid_update_mmtaux'_unfolded[OF assms]
    by auto
  ultimately show ?thesis
    unfolding auxlist'_def
    by force
qed

fun update_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mmtaux" where
  "update_mmtaux args nt l r (cur, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) = (
  let (idx_mid', idx_oldest', data_prev', data_in', tuple_in_once', tuple_in_once_keys', tuple_since_hist', hist_sat', since_sat') =
    update_mmtaux' args nt idx_mid idx_oldest maskL maskR data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat
  in (
    if mem (args_ivl args) 0 then (
      let tuple_since_hist'' = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist' in
        (
          nt,
          idx_next+1,
          idx_mid'+1,
          idx_oldest',
          maskL,
          maskR,
          data_prev',
          (append_queue (nt, r) data_in'),
          tuple_in_once',
          tuple_in_once_keys',
          upd_set tuple_since_hist'' (\<lambda>_. idx_mid') (r - Mapping.keys tuple_since_hist''),
          (if is_empty data_in' then r else hist_sat' \<inter> r),
          (since_sat' \<inter> r) \<union> {as \<in> r. proj_tuple_in_join (args_pos args) maskL as l}
        )
      )
    else
      (
        nt,
        idx_next+1,
        idx_mid',
        idx_oldest',
        maskL,
        maskR,
        append_queue (nt, l, r) data_prev',
        data_in',
        upd_set tuple_in_once' (\<lambda>_. nt) l,
        tuple_in_once_keys' \<union> l,
        tuple_since_hist',
        hist_sat',
        since_sat'
      )
  ))"

lemma valid_update_mmtaux_unfolded:
  assumes "nt \<ge> cur"
  assumes "table (args_n args) (args_L args) l"
  assumes "table (args_n args) (args_R args) r"
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat) auxlist"
    shows "valid_mmtaux
      args
      nt
      (update_mmtaux args nt l r (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat))
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "
proof -
  define update_mmtaux'_res
    where "update_mmtaux'_res = update_mmtaux' args nt idx_mid idx_oldest maskL maskR data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat"

  define idx_mid' where "idx_mid' = fst update_mmtaux'_res"
  define idx_oldest' where "idx_oldest' = (fst o snd) update_mmtaux'_res"
  define data_prev' where "data_prev' = (fst o snd o snd) update_mmtaux'_res"
  define data_in' where "data_in' = (fst o snd o snd o snd) update_mmtaux'_res"
  define tuple_in_once' where "tuple_in_once' = (fst o snd o snd o snd o snd) update_mmtaux'_res"
  define tuple_in_once_keys' where "tuple_in_once_keys' = (fst o snd o snd o snd o snd o snd) update_mmtaux'_res"
  define tuple_since_hist' where "tuple_since_hist'     = (fst o snd o snd o snd o snd o snd o snd) update_mmtaux'_res"
  define hist_sat' where "hist_sat'                     = (fst o snd o snd o snd o snd o snd o snd o snd) update_mmtaux'_res"
  define since_sat' where "since_sat'                   = (snd o snd o snd o snd o snd o snd o snd o snd) update_mmtaux'_res"

  define auxlist' where "auxlist' = filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist"

  have update_eq: "(idx_mid', idx_oldest', data_prev', data_in', tuple_in_once', tuple_in_once_keys', tuple_since_hist', hist_sat', since_sat') =
    update_mmtaux' args nt idx_mid idx_oldest maskL maskR data_prev data_in tuple_in_once tuple_in_once_keys tuple_since_hist hist_sat since_sat"
    using update_mmtaux'_res_def
    unfolding idx_mid'_def idx_oldest'_def data_prev'_def data_in'_def tuple_in_once'_def tuple_in_once_keys'_def tuple_since_hist'_def hist_sat'_def since_sat'_def
    by auto

  have valid: "valid_mmtaux args nt (nt, idx_next, idx_mid', idx_oldest', maskL, maskR, data_prev', data_in', tuple_in_once', tuple_in_once_keys', tuple_since_hist', hist_sat', since_sat')
     auxlist'"
    unfolding auxlist'_def
    using valid_update_mmtaux'[OF assms(4) assms(1) update_eq]
    by blast

  define update_mmtaux_res where "update_mmtaux_res = update_mmtaux args nt l r (cur, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"
  define auxlist'' where "auxlist'' = auxlist' @ [(nt, l, r)]"

  have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
    using valid
    by auto
  then have data_in'_len_leq: "length (linearize data_in') \<le> length auxlist'"
    unfolding auxlist_data_in_def
    by (metis (no_types, lifting) length_filter_le length_map)

  from assms(4) have maskL: "maskL = join_mask (args_n args) (args_L args)"
    by auto

  then have proj_l: "\<forall>as \<in> l. as = proj_tuple maskL as"
    using assms(2)
    unfolding table_def
    using wf_tuple_proj_idle[of "args_n args" "args_L args"]
    by metis


  show ?thesis
  proof (cases "mem (args_ivl args) 0")    
    case True

    define idx_mid'' where "idx_mid'' = idx_mid'+1"
    define idx_next'' where "idx_next'' = idx_next+1"
    define data_in'' where "data_in'' = (append_queue (nt, r) data_in')"
    define tuple_since_hist'' where "tuple_since_hist'' = Mapping.filter (\<lambda>as _. as \<in> r) tuple_since_hist'"
    define tuple_since_hist''' where "tuple_since_hist''' = upd_set tuple_since_hist'' (\<lambda>_. idx_mid') (r - Mapping.keys tuple_since_hist'')"
    define hist_sat'' where "hist_sat'' = (if is_empty data_in' then r else hist_sat' \<inter> r)"
    define since_sat'' where "since_sat'' = (since_sat' \<inter> r) \<union> {as \<in> r. proj_tuple_in_join (args_pos args) maskL as l}"

    have res_eq: "(
        nt,
        idx_next'',
        idx_mid'',
        idx_oldest',
        maskL,
        maskR,
        data_prev',
        data_in'',
        tuple_in_once',
        tuple_in_once_keys',
        tuple_since_hist''',
        hist_sat'',
        since_sat''
      ) = update_mmtaux args nt l r (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"
      unfolding update_mmtaux_res_def idx_mid''_def idx_next''_def data_in''_def tuple_since_hist'''_def tuple_since_hist''_def hist_sat''_def since_sat''_def
      using True
      by (auto simp only: update_mmtaux.simps Let_def update_eq[symmetric] split: if_splits)

    have auxlist_in_eq: "(auxlist_data_in args nt auxlist'') = (auxlist_data_in args nt auxlist') @ [(nt, l, r)]"
      using True
      unfolding auxlist_data_in_def auxlist''_def
      by auto

    have auxlist_prev_eq: "(auxlist_data_prev args nt auxlist'') = (auxlist_data_prev args nt auxlist')"
      using True
      unfolding auxlist_data_prev_def auxlist''_def
      by auto

    have "auxlist_data_prev args nt auxlist' = (linearize data_prev')"
      using valid
      by auto
    moreover have memL: "\<forall>t. memL (args_ivl args) t"
      using True
      by auto
    ultimately have lin_data_prev'_eq:
      "(linearize data_prev') = []"
      "auxlist_data_prev args nt auxlist' = []"
      unfolding auxlist_data_prev_def
      by auto
    moreover have "auxlist_data_prev args nt auxlist' = drop (length (linearize data_in')) auxlist'"
      using valid
      by auto
    ultimately have data_in'_len:"length (linearize data_in') = length auxlist'"
      using data_in'_len_leq
      by auto
    moreover have "auxlist_data_in args nt auxlist' = take (length (linearize data_in')) auxlist'"
      using valid
      by auto
    ultimately have auxlist_in_eq:
      "auxlist_data_in args nt auxlist' = auxlist'"
      "auxlist_data_in args nt auxlist'' = auxlist' @ [(nt, l, r)]"
      using auxlist_in_eq
      by auto

    have "(if mem (args_ivl args) 0 then (args_L args) \<subseteq> (args_R args) else (args_L args) = (args_R args))"
      using assms(4)
      by auto
    moreover have "\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args"
      using assms(4)
      by auto
    moreover have "maskL = join_mask (args_n args) (args_L args)"
      using assms(4)
      by auto
    moreover have "maskR = join_mask (args_n args) (args_R args)"
      using assms(4)
      by auto
    moreover have "(\<forall>(t, relL, relR) \<in> set auxlist''. table (args_n args) (args_L args) relL \<and> table (args_n args) (args_R args) relR)"
    proof -
      have "(\<forall>(t, relL, relR) \<in> set auxlist'. table (args_n args) (args_L args) relL \<and> table (args_n args) (args_R args) relR)"
        using valid
        by auto
      then show ?thesis using assms(2-3) unfolding auxlist''_def by auto
    qed
    moreover have "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
      using valid
      by auto
    moreover have "table (args_n args) (args_R args) (Mapping.keys tuple_since_hist''')"
    proof -
      have "table (args_n args) (args_R args) (Mapping.keys tuple_since_hist')"
        using valid
        by auto
      then have "table (args_n args) (args_R args) (Mapping.keys tuple_since_hist'')"
        unfolding tuple_since_hist''_def
        by (meson New_max.wf_atable_subset keys_filter)
      moreover have "table (args_n args) (args_R args) (r - Mapping.keys tuple_since_hist'')"
        using assms(3)
        unfolding table_def
        by (meson DiffD1)
      ultimately show ?thesis
        unfolding tuple_since_hist'''_def
        by (metis Mapping_upd_set_keys table_Un)
    qed
    moreover have "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_L args) as)"
      using valid
      by auto
    moreover have "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as)"
      using valid
      by auto
    moreover have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in''))). wf_tuple (args_n args) (args_R args) as)"
    proof -
      have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in'))). wf_tuple (args_n args) (args_R args) as)"
        using valid
        by auto
      then show ?thesis
        using assms(3)
        unfolding data_in''_def append_queue_rep table_def
        by auto
    qed
    moreover have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist'')) =
      ts_tuple_rel (set (linearize data_in''))"
    proof -
      have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist')) =
      ts_tuple_rel (set (linearize data_in'))"
        using valid
        by auto
      moreover have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist'')) = ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist')) \<union> ts_tuple_rel_binary_rhs (set ([(nt, l, r)]))"
        using auxlist_in_eq
        unfolding ts_tuple_rel_f_def
        by auto
      moreover have "ts_tuple_rel (set (linearize data_in'')) = ts_tuple_rel (set (linearize data_in')) \<union> ts_tuple_rel (set [(nt, r)])"
        unfolding data_in''_def ts_tuple_rel_f_def append_queue_rep
        by auto
      ultimately show ?thesis
        unfolding ts_tuple_rel_f_def
        by auto
    qed
    moreover have "sorted (map fst auxlist'')"
    proof -
      have
        "sorted (map fst auxlist')"
        "\<forall>db \<in> set auxlist'. time db \<le> nt"
        using valid
        by auto
      then show ?thesis
        unfolding auxlist''_def time_def
        using sorted_append[of "map fst auxlist'" "map fst [(nt, l, r)]"]
        by auto
    qed
    moreover have "auxlist_data_prev args nt auxlist'' = (linearize data_prev')"
      unfolding auxlist_prev_eq
      using valid
      by auto
    moreover have "auxlist_data_prev args nt auxlist'' = drop (length (linearize data_in'')) auxlist''"
      using True data_in'_len memL
      unfolding auxlist''_def data_in''_def append_queue_rep auxlist_data_prev_def
      by auto
    moreover have "length (linearize data_prev') + idx_mid'' = idx_next''"
      using valid
      unfolding idx_mid''_def idx_next''_def
      by auto
    moreover have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist'') = (linearize data_in'')"
    proof -
      have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
        using valid
        by auto
     then show ?thesis
      unfolding auxlist_in_eq data_in''_def append_queue_rep
      by auto
    qed
    moreover have "auxlist_data_in args nt auxlist'' = take (length (linearize data_in'')) auxlist''"
      unfolding auxlist_in_eq(2) data_in''_def append_queue_rep
      unfolding auxlist''_def
      using take_append[of "length auxlist'" auxlist' "[(nt, l, r)]"] length_append[of "linearize data_in'" "[(nt, r)]"]
      by (simp add: data_in'_len)
    moreover have data_in''_len: "length (linearize data_in'') + idx_oldest' = idx_mid''"
    proof -
      have "length (linearize data_in') + idx_oldest' = idx_mid'"
        using valid
        by auto
      then show ?thesis
        unfolding idx_mid''_def data_in''_def append_queue_rep
        by auto
    qed
    moreover have "(\<forall>db \<in> set auxlist''. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
    proof -
      have "(\<forall>db \<in> set auxlist'. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
        using valid
        by auto
      then show ?thesis
        unfolding auxlist''_def time_def
        by auto
    qed
    moreover have "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
      using valid
      by auto
    moreover have "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l (proj_tuple maskL as))"
      using valid
      by auto
    moreover have "(\<forall>as. (case Mapping.lookup tuple_since_hist''' as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx)
    )"
    proof -
      have before: "(\<forall>as. (case Mapping.lookup tuple_since_hist' as of
        Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx
        | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx)
      )"
        using valid
        by auto
      have non_empty: "linearize data_in'' \<noteq> []"
        unfolding data_in''_def append_queue_rep
        by auto
      have data_in''_last: "last (linearize data_in'') = (nt, r)"
        unfolding data_in''_def append_queue_rep
        by auto
      have before_len:
        "length (linearize data_in') + idx_oldest' = idx_mid'"
        using valid
        by auto
      {
        fix as
        have "(case Mapping.lookup tuple_since_hist''' as of
          Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx
          | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx)"
        proof (cases "Mapping.lookup tuple_since_hist''' as")
          case None
          then have
            "as \<notin> (r - Mapping.keys tuple_since_hist'')"
            unfolding tuple_since_hist'''_def
            by (metis Mapping_lookup_upd_set option.simps(3))
          moreover have hist'': "Mapping.lookup tuple_since_hist'' as = None"
            using None
            unfolding tuple_since_hist'''_def
            by (metis Mapping_lookup_upd_set option.simps(3))
          ultimately have not_relR: "as \<notin> r"
            by (simp add: keys_is_none_rep)
          
          {
            fix idx
            assume "idx < idx_mid''"
            then have "last (linearize data_in'') \<in> set (drop (idx - idx_oldest') (linearize data_in''))"
              using non_empty data_in''_len
              by (metis add.commute add_diff_inverse_nat add_less_cancel_left diff_is_0_eq dual_order.strict_iff_order last_drop last_in_set length_drop length_greater_0_conv zero_less_diff)
            moreover have "as \<notin> snd (last (linearize data_in''))"
            using not_relR data_in''_last
              by simp
            ultimately have "\<not>(\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in'')). as \<in> y)"
              by fastforce
          }
          then have "\<forall>idx. \<not> tuple_since_tp args as (linearize data_in'') (idx_oldest') (idx_mid'') idx"
            unfolding tuple_since_tp_def
            by auto

          then show ?thesis using None by auto
        next
          case (Some idx)
          then have "tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx"
          proof (cases "as \<in> (r - Mapping.keys tuple_since_hist'')")
            case True
            then have idx_eq: "idx = idx_mid'"
              using Some
              unfolding tuple_since_hist'''_def
              by (simp add: Mapping_lookup_upd_set)
            then have drop_eq: "drop (idx - idx_oldest') (linearize data_in'') = [(nt, r)]"
              using data_in''_len
              unfolding idx_mid''_def data_in''_def append_queue_rep
              by auto
            then have "\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in'')). as \<in> y"
              using True
              by auto
            moreover have "idx_oldest' < idx \<longrightarrow> as \<notin> snd (linearize data_in'' ! (idx - idx_oldest' - 1))"
            proof -
              {
                assume assm: "idx_oldest' < idx"
                then have before_non_empty: "linearize data_in' \<noteq> []"
                  using before_len idx_eq
                  by auto
                have "Mapping.lookup tuple_since_hist' as = None"
                  using True
                  unfolding tuple_since_hist''_def
                  by (metis DiffD1 DiffD2 Mapping_keys_intro Mapping_lookup_filter_Some)
                then have not_hist: "\<forall>idx. \<not> tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx"
                  using before
                  by (simp add: option.case_eq_if)

                have "as \<notin> snd (last (linearize data_in'))"
                  using no_hist_last_not_sat[OF before_len not_hist before_non_empty]
                  by auto
                then have "as \<notin> snd (linearize data_in'' ! (idx - idx_oldest' - 1))"
                  using data_in'_len idx_eq
                  unfolding data_in''_def
                  by (metis add_diff_cancel_right' append_eq_conv_conj append_queue_rep assm before_len before_non_empty diff_less last_conv_nth leI not_one_le_zero nth_take zero_less_diff)
              }
              then show ?thesis by auto
            qed
            ultimately have "tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx"
              using non_empty idx_eq
              unfolding tuple_since_tp_def idx_mid''_def
              by auto
            then show ?thesis
              by auto
          next
            case False
            then have "Mapping.lookup tuple_since_hist'' as = Some idx"
              using Some
              unfolding tuple_since_hist'''_def
              by (metis Mapping_lookup_upd_set)
            then have as_mem:
              "as \<in> r \<and> Mapping.lookup tuple_since_hist' as = Some idx"
              unfolding tuple_since_hist''_def
              by (metis Mapping_lookup_filter_None Mapping_lookup_filter_not_None option.simps(3))

            then have tuple_since: "tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx"
              using before
              by (auto split: option.splits)
            then have idx_props:
              "idx < idx_mid'"
              "\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in')). as \<in> y"
              "idx_oldest' < idx \<longrightarrow> as \<notin> snd (linearize data_in' ! (idx - idx_oldest' - 1))"
              unfolding tuple_since_tp_def
              by auto

            have "idx - idx_oldest' \<le> length (linearize data_in')"
              using before_len idx_props(1)
              by auto
            then have "\<forall>(t, y)\<in>set (drop (idx - idx_oldest') (linearize data_in'')). as \<in> y"
              using idx_props(2) as_mem
              unfolding data_in''_def append_queue_rep
              by auto
            moreover have "linearize data_in'' ! (idx - idx_oldest' - 1) = linearize data_in' ! (idx - idx_oldest' - 1)"
              using before_len idx_props
              unfolding data_in''_def append_queue_rep
              by (metis (no_types, lifting) diff_is_0_eq idx_append not_le_imp_less length_greater_0_conv less_diff_conv2 less_imp_diff_less less_or_eq_imp_le tuple_since tuple_since_tp_def)

            ultimately have "tuple_since_tp args as (linearize data_in'') idx_oldest' idx_mid'' idx"
              using non_empty idx_props
              unfolding tuple_since_tp_def idx_mid''_def
              by auto
            then show ?thesis by auto
          qed
          then show ?thesis
            using Some
            by auto
        qed
      }
      
      then show ?thesis
        by auto
    qed
    moreover have "(\<forall>tuple. tuple \<in> hist_sat'' \<longleftrightarrow>
        (\<not>is_empty data_in'') \<and> (
          \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
      ))"
    proof -
      have before: "(\<forall>tuple. tuple \<in> hist_sat' \<longleftrightarrow>
        (\<not>is_empty data_in') \<and> (
          \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r
      ))"
        using valid
        by auto
      {
        fix tuple

        {
          assume assm: "is_empty data_in'"
          have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
            using valid
            by auto
          then have "(auxlist_data_in args nt auxlist') = []"
            using assm is_empty_alt[of data_in']
            by auto
          then have "auxlist_data_in args nt auxlist'' = [(nt, l, r)]"
            using auxlist_in_eq
            by auto
        }
        then have empty_data_in': "is_empty data_in' \<longrightarrow> auxlist_data_in args nt auxlist'' = [(nt, l, r)]"
          by auto

        have "tuple \<in> hist_sat'' \<longleftrightarrow>
          (\<not>is_empty data_in'') \<and> (
            \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
        )"
        proof (rule iffI)
          assume assm: "tuple \<in> hist_sat''"
          show "(\<not>is_empty data_in'') \<and> (
              \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
          )"
          proof (cases "is_empty data_in'")
            case True
            then have tuple_mem: "tuple \<in> r"
              using assm
              unfolding hist_sat''_def
              by auto
            
            then have "\<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r"
              using empty_data_in' True tuple_mem
              by auto
            moreover have "linearize data_in'' \<noteq> []"
              unfolding data_in''_def append_queue_rep
              by auto
            ultimately show ?thesis
              using is_empty_alt
              by auto
          next
            case False
            then have tuple_mem:
              "tuple \<in> hist_sat'"
              "tuple \<in> r"
              using assm
              unfolding hist_sat''_def
              by auto
            then have props: "(\<not>is_empty data_in') \<and> (
                \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r
            )"
              using before
              by auto
            then have all: "\<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r"
              using tuple_mem(2)
              unfolding auxlist_in_eq set_append
              by auto
  
            have "linearize data_in' \<noteq> []"
              using props is_empty_alt
              by auto
            then have "linearize data_in'' \<noteq> []"
              unfolding data_in''_def append_queue_rep
              by auto
            then show ?thesis
              using all is_empty_alt
              by auto
          qed
        next
          assume assm: "(\<not>is_empty data_in'') \<and> (
              \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
          )"
          then show "tuple \<in> hist_sat''"
          proof (cases "is_empty data_in'")
            case True
            then have "tuple \<in> r"
              using assm empty_data_in'
              by auto
            then show ?thesis
              unfolding hist_sat''_def
              using True
              by auto
          next
            case False
            then have tuple_mem:
              "tuple \<in> r"
              "\<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r"
              using assm auxlist_in_eq
              by auto
            then have "tuple \<in> hist_sat'"
              using before False
              by auto
            then show ?thesis
              unfolding hist_sat''_def
              using False tuple_mem(1)
              by auto
          qed
        qed
      }
      then show ?thesis by auto
    qed
    moreover have "(\<forall>tuple. tuple \<in> since_sat'' \<longrightarrow>
        ((tuple \<in> hist_sat'') \<or> tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist''))
      )"
    proof -
      have before: "(\<forall>tuple. tuple \<in> since_sat' \<longrightarrow>
          ((tuple \<in> hist_sat') \<or> tuple_since_lhs tuple (linearize data_in') args maskL (auxlist_data_in args nt auxlist'))
        )"
        using valid
        unfolding valid_mmtaux.simps
        apply -
        apply (erule conjE)+
        apply assumption
        done
      {
        fix tuple
        assume assm: "tuple \<in> since_sat''"
        have non_empty: "linearize data_in'' \<noteq> []"
          unfolding data_in''_def append_queue_rep
          by auto
        have "tuple \<in> (since_sat' \<inter> r) \<union> {as \<in> r. proj_tuple_in_join (args_pos args) maskL as l}"
          using assm since_sat''_def
          by auto
        moreover {
          assume assm: "tuple \<in> (since_sat' \<inter> r)"
          then have "tuple \<in> hist_sat' \<or> tuple_since_lhs tuple (linearize data_in') args maskL (auxlist_data_in args nt auxlist')"
            using before
            by auto
          moreover {
            assume hist: "tuple \<in> hist_sat'"
            moreover have "(\<forall>tuple. tuple \<in> hist_sat' \<longleftrightarrow>
              (\<not>is_empty data_in') \<and> (
                \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist'). tuple \<in> r
            ))"
              using valid
              by auto
            ultimately have "(\<not>is_empty data_in')"
              by auto
            then have "tuple \<in> hist_sat''"
              using assm hist
              unfolding hist_sat''_def
              by auto
          }
          moreover {
            assume since: "tuple_since_lhs tuple (linearize data_in') args maskL (auxlist_data_in args nt auxlist')"
            then have "linearize data_in' \<noteq> []"
              unfolding tuple_since_lhs_def
              by auto
            obtain n where n_props:
              "n\<in>{0..<length (linearize data_in')}"
              "let suffix = drop n (auxlist_data_in args nt auxlist') in (\<forall>(t, l, y)\<in>set suffix. tuple \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)"
              using since
              unfolding tuple_since_lhs_def
              by auto
            
            have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
              using valid
              by auto
            then have len_eq: "length (auxlist_data_in args nt auxlist') = length (linearize data_in')"
              using length_map
              by metis
            then have n_le: "n < length (auxlist_data_in args nt auxlist')"
              using n_props(1)
              by auto
            moreover have "(auxlist_data_in args nt auxlist'') = (auxlist_data_in args nt auxlist') @ [(nt, l, r)]"
              using auxlist_in_eq
              by auto
            ultimately have drop_eq: "drop n (auxlist_data_in args nt auxlist'') = drop n (auxlist_data_in args nt auxlist') @ [(nt, l, r)]"
              by auto

            have "let suffix = drop n (auxlist_data_in args nt auxlist'') in (\<forall>(t, l, y)\<in>set suffix. tuple \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)"
              using n_props(2) n_le len_eq assm
              unfolding drop_eq Let_def
              by auto
            moreover have "n\<in>{0..<length (linearize data_in'')}"
              using n_props(1)
              unfolding data_in''_def append_queue_rep
              by auto
            ultimately have "tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist'')"
              using non_empty
              unfolding tuple_since_lhs_def
              by blast
          }
          ultimately have "tuple \<in> hist_sat'' \<or> tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist'')"
            by auto
        }
        moreover {
          define n where "n = length (auxlist_data_in args nt auxlist'') - 1"
          assume "tuple \<in> {as \<in> r. proj_tuple_in_join (args_pos args) maskL as l}"
          then have tuple_props: "tuple \<in> r" "proj_tuple_in_join (args_pos args) maskL tuple l"
            by auto
          have drop_eq: "drop n (auxlist_data_in args nt auxlist'') = [(nt, l, r)]"
            unfolding n_def
            using auxlist_in_eq
            by auto
          have "\<forall>(t, l, y)\<in>set (drop n (auxlist_data_in args nt auxlist'')). tuple \<in> y"
            using drop_eq tuple_props
            by auto
          moreover have "join_cond (args_pos args) (relL (hd (drop n (auxlist_data_in args nt auxlist'')))) (proj_tuple maskL tuple)"
            using tuple_props
            unfolding drop_eq relL_def
            by (simp add: proj_tuple_in_join_def)
          moreover have "n\<in>{0..<length (linearize data_in'')}"
          proof -
            have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
              using valid
              by auto
            then show ?thesis
              using auxlist_in_eq length_map[of "(\<lambda>(t, l, r). (t, r))" "(auxlist_data_in args nt auxlist')"]
              unfolding data_in''_def append_queue_rep n_def
              by auto
          qed
          ultimately have "tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist'')"
            using non_empty
            unfolding tuple_since_lhs_def
            by (auto simp add: Let_def)
        }
        ultimately have "tuple \<in> hist_sat'' \<or> tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist'')"
          by auto
      }
      then show ?thesis by auto
    qed
    moreover have "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist'') \<longrightarrow>
        tuple \<in> since_sat''
      )"
    proof -
      have before: "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in') args maskL (auxlist_data_in args nt auxlist') \<longrightarrow>
        tuple \<in> since_sat'
      )"
        using valid
        by auto
      {
        fix tuple
        assume assm: "tuple_since_lhs tuple (linearize data_in'') args maskL (auxlist_data_in args nt auxlist'')"
        then have non_empty: "linearize data_in'' \<noteq> []"
          unfolding tuple_since_lhs_def
          by auto
        obtain n where n_props:
          "n\<in>{0..<length (linearize data_in'')}"
          "let suffix = drop n (auxlist_data_in args nt auxlist'') in (\<forall>(t, l, y)\<in>set suffix. tuple \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)"
          using assm
          unfolding tuple_since_lhs_def
          by auto
        {
          assume n_l: "n\<in>{0..<length (linearize data_in')}"
          then have "length (drop n auxlist') > 0"
            using data_in'_len
            by auto
          
          moreover have "set (drop n (auxlist_data_in args nt auxlist')) \<subseteq> set (drop n (auxlist_data_in args nt auxlist''))"
            using auxlist_in_eq Let_def
            by (auto simp add: data_in'_len)
          ultimately have "let suffix = drop n (auxlist_data_in args nt auxlist') in (\<forall>(t, l, y)\<in>set suffix. tuple \<in> y) \<and> join_cond (args_pos args) (relL (hd suffix)) (proj_tuple maskL tuple)"
            using n_props(2) n_l
            unfolding auxlist_in_eq Let_def
            by auto
          
          moreover have "linearize data_in' \<noteq> []"
            using n_l
            by auto
          ultimately have "tuple \<in> since_sat'"
            using n_l before
            unfolding tuple_since_lhs_def
            by blast
          moreover have "tuple \<in> r"
            using n_l n_props auxlist_in_eq
            apply (auto simp add: data_in'_len)
            by meson
          ultimately have "tuple \<in> since_sat' \<inter> r"
            by auto
        }
        moreover {
          assume "n \<notin> {0..<length (linearize data_in')}"
          then have "n = length (linearize data_in')"
            using n_props
            unfolding data_in''_def append_queue_rep
            by auto
          moreover have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist') = (linearize data_in')"
            using valid
            by auto
          ultimately have "drop n (auxlist_data_in args nt auxlist'') = [(nt, l, r)]"
            using auxlist_in_eq length_map[of "(\<lambda>(t, l, r). (t, r))" "(auxlist_data_in args nt auxlist')"]
            by auto
          then have "tuple \<in> r" "join_cond (args_pos args) l (proj_tuple maskL tuple)"
            using n_props(2)
            unfolding relL_def
            by (auto simp add: Let_def)
          then have "tuple \<in> {as \<in> r. proj_tuple_in_join (args_pos args) maskL as l}"
            unfolding proj_tuple_in_join_def
            by auto
        }
        ultimately have "tuple \<in> since_sat''"
          unfolding since_sat''_def
          by auto
      }
      then show ?thesis by auto
    qed
    moreover have "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
      using valid
      by auto
    moreover have "time (nt, l, r) \<le> nt"
      unfolding time_def
      by auto
    ultimately show ?thesis
      unfolding res_eq[symmetric] auxlist''_def auxlist'_def
      by (auto simp only: valid_mmtaux.simps)
  next
    case False
    define data_prev'' where "data_prev'' = (append_queue (nt, l, r) data_prev')"
    define idx_next'' where "idx_next'' = idx_next+1"
    define tuple_in_once'' where "tuple_in_once'' = upd_set tuple_in_once' (\<lambda>_. nt) l"
    define tuple_in_once_keys'' where "tuple_in_once_keys'' = tuple_in_once_keys' \<union> l"

    have auxlist_in_eq: "(auxlist_data_in args nt auxlist'') = (auxlist_data_in args nt auxlist')"
      using False
      unfolding auxlist_data_in_def auxlist''_def
      by auto

    have auxlist_prev_eq: "(auxlist_data_prev args nt auxlist'') = (auxlist_data_prev args nt auxlist') @ [(nt, l, r)]"
      using False
      unfolding auxlist_data_prev_def auxlist''_def
      by auto

    have res_eq: "(
        nt,
        idx_next'',
        idx_mid',
        idx_oldest',
        maskL,
        maskR,
        data_prev'',
        data_in',
        tuple_in_once'',
        tuple_in_once_keys'',
        tuple_since_hist',
        hist_sat',
        since_sat'
      ) = update_mmtaux args nt l r (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_in_once_keys, tuple_since_hist, hist_sat, since_sat)"
      unfolding update_mmtaux_res_def data_prev''_def idx_next''_def tuple_in_once''_def tuple_in_once_keys''_def
      using False
      by (auto simp only: update_mmtaux.simps Let_def update_eq[symmetric] split: if_splits)
  
    have "(if mem (args_ivl args) 0 then (args_L args) \<subseteq> (args_R args) else (args_L args) = (args_R args))"
      using assms(4)
      by auto
    moreover have "\<not>mem (args_ivl args) 0 \<longrightarrow> args_pos args"
      using assms(4)
      by auto
    moreover have "maskL = join_mask (args_n args) (args_L args)"
      using assms(4)
      by auto
    moreover have "maskR = join_mask (args_n args) (args_R args)"
      using assms(4)
      by auto
    moreover have "(\<forall>(t, relL, relR) \<in> set auxlist''. table (args_n args) (args_L args) relL \<and> table (args_n args) (args_R args) relR)"
    proof -
      have "(\<forall>(t, relL, relR) \<in> set auxlist'. table (args_n args) (args_L args) relL \<and> table (args_n args) (args_R args) relR)"
        using valid
        by auto
      then show ?thesis using assms(2-3) unfolding auxlist''_def by auto
    qed
    moreover have table_in_once'': "table (args_n args) (args_L args) (Mapping.keys tuple_in_once'')"
    proof -
      have "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
        using valid
        by auto
      then show ?thesis
        unfolding tuple_in_once''_def
        using assms(2)
        by (simp add: Mapping_upd_set_keys)
    qed
    moreover have "table (args_n args) (args_R args) (Mapping.keys tuple_since_hist')"
      using valid
      by auto
    moreover have data_prev''_relL: "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev''))). wf_tuple (args_n args) (args_L args) as)"
    proof -
      have "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_L args) as)"
        using valid
        by auto
      then show ?thesis
        using assms(2)
        unfolding data_prev''_def append_queue_rep relL_def table_def
        by auto
    qed
    moreover have "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev''))). wf_tuple (args_n args) (args_R args) as)"
    proof -
      have "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as)"
        using valid
        by auto
      then show ?thesis
        using assms(3)
        unfolding data_prev''_def append_queue_rep relR_def table_def
        by auto
    qed
    moreover have "(\<forall>as \<in> \<Union>((snd) ` (set (linearize data_in'))). wf_tuple (args_n args) (args_R args) as)"
      using valid
      by auto
    moreover have "ts_tuple_rel_binary_rhs (set (auxlist_data_in args nt auxlist'')) =
      ts_tuple_rel (set (linearize data_in'))"
      unfolding auxlist_in_eq
      using valid
      by auto
    moreover have "sorted (map fst auxlist'')"
    proof -
      have
        "sorted (map fst auxlist')"
        "\<forall>db \<in> set auxlist'. time db \<le> nt"
        using valid
        by auto
      then show ?thesis
        unfolding auxlist''_def time_def
        using sorted_append[of "map fst auxlist'" "map fst [(nt, l, r)]"]
        by auto
    qed
    moreover have data_prev''_auxlist: "auxlist_data_prev args nt auxlist'' = (linearize data_prev'')"
    proof -
      have "auxlist_data_prev args nt auxlist' = (linearize data_prev')"
        using valid
        by auto
      then show ?thesis
        using False
        unfolding auxlist_data_prev_def auxlist''_def data_prev''_def append_queue_rep
        by auto
    qed
    moreover have "auxlist_data_prev args nt auxlist'' = drop (length (linearize data_in')) auxlist''"
    proof - 
      have "auxlist_data_prev args nt auxlist' = drop (length (linearize data_in')) auxlist'"
        using valid
        by auto
      then show ?thesis
        using False data_in'_len_leq
        unfolding auxlist''_def auxlist_data_prev_def
        by auto
    qed
    moreover have "length (linearize data_prev'') + idx_mid' = idx_next''"
    proof -
      have "length (linearize data_prev') + idx_mid' = idx_next"
        using valid
        by auto
      then show ?thesis
        unfolding data_prev''_def idx_next''_def append_queue_rep
        by auto
    qed
    moreover have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args nt auxlist'') = (linearize data_in')"
      unfolding auxlist_in_eq
      using valid
      by auto
    moreover have "auxlist_data_in args nt auxlist'' = take (length (linearize data_in')) auxlist''"
    proof -
      have "auxlist_data_in args nt auxlist' = take (length (linearize data_in')) auxlist'"
        using valid
        by auto
      then show ?thesis
        using data_in'_len_leq False
        unfolding auxlist''_def auxlist_data_in_def
        by auto
    qed
    moreover have "length (linearize data_in') + idx_oldest' = idx_mid'"
      using valid
      by auto
    moreover have "(\<forall>db \<in> set auxlist''. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
    proof -
      have "(\<forall>db \<in> set auxlist'. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
        using valid
        by auto
      then show ?thesis
        unfolding auxlist''_def time_def
        by auto
    qed
    moreover have "newest_tuple_in_mapping fst data_prev'' tuple_in_once'' (\<lambda>x. True)"
    proof -
      have before: "newest_tuple_in_mapping fst data_prev' tuple_in_once' (\<lambda>x. True)"
        using valid
        by auto
      {
        fix tuple::"'a option list"
        assume wf: "wf_tuple (args_n args) (args_L args) tuple"

        have ts_rel_union: "ts_tuple_rel_binary_lhs (set (linearize data_prev'')) = ts_tuple_rel_binary_lhs (set (linearize data_prev')) \<union> ts_tuple_rel_binary_lhs (set [(nt, l, r)])"
          unfolding ts_tuple_rel_f_def data_prev''_def append_queue_rep
          by auto

        have tuple_not_mem_empty: "tuple \<notin> l \<longrightarrow> {tas \<in> ts_tuple_rel_binary_lhs (set [(nt, l, r)]). proj_tuple maskL tuple = snd tas} = {}"
          proof -
            {
              assume tuple_not_mem: "tuple \<notin> l"
              assume "{tas \<in> ts_tuple_rel_binary_lhs (set [(nt, l, r)]). True \<and> proj_tuple maskL tuple = snd tas} \<noteq> {}"
              then obtain t as where as_props: "(t, as) \<in> ts_tuple_rel_binary_lhs (set [(nt, l, r)])" "proj_tuple maskL tuple = as"
                by auto
              then have as_eq: "tuple = as"
                using maskL wf_tuple_proj_idle[OF wf]
                by auto
              obtain l' r' where "as \<in> l'" "(t, l', r') \<in> set [(nt, l, r)]"
                using as_props 
                unfolding ts_tuple_rel_f_def
                by auto
              then have "as \<in> l"
                by auto
              then have "False"
                using as_eq tuple_not_mem
                by auto
            }
            then show ?thesis by auto
          qed

        have "Mapping.lookup tuple_in_once'' tuple = safe_max (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas})"
        proof (cases "Mapping.lookup tuple_in_once'' tuple")
          case None
          have tuple_not_mem: "tuple \<notin> l"
            using None
            unfolding tuple_in_once''_def
            by (metis Mapping_lookup_upd_set option.distinct(1))
          have "Mapping.lookup tuple_in_once' tuple = None"
            using None
            unfolding tuple_in_once''_def
            by (metis Mapping_lookup_upd_set option.distinct(1))
          then have "{tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). tuple = snd tas} = {}"
            using before
            unfolding newest_tuple_in_mapping_def safe_max_def
            apply (auto split: option.splits)
            by (metis (no_types) option.distinct(1))
          then have "\<forall>tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). tuple \<noteq> snd tas" 
            by blast
          then have "fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} = {}"
            using tuple_not_mem tuple_not_mem_empty
            unfolding data_prev''_def append_queue_rep ts_tuple_rel_f_def
            by auto
          then show ?thesis
            using None
            unfolding safe_max_def
            by (auto split: if_splits)
        next
          case (Some t)
          then show ?thesis
          proof (cases "tuple \<in> l")
            case True
            then have t_eq: "t = nt"
              using Some
              unfolding tuple_in_once''_def
              by (simp add: Mapping_lookup_upd_set)
            have "(nt, tuple) \<in> ts_tuple_rel_binary_lhs (set [(nt, l, r)])"
              using True
              unfolding ts_tuple_rel_f_def
              by auto
            then have "(nt, tuple) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev''))"
              using ts_rel_union
              by auto
            then have nt_mem: "nt \<in> fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas}"
              using proj_l True
              by (metis (mono_tags) fst_conv imageI mem_Collect_eq snd_conv)

            then have non_empty: "fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} \<noteq> {}"
              by auto

            have "\<forall>t \<in> fst ` ts_tuple_rel_binary_lhs (set [(nt, l, r)]). t \<le> nt"
              unfolding ts_tuple_rel_f_def
              by auto
            moreover have "\<forall>t \<in> fst ` ts_tuple_rel_binary_lhs (set (linearize data_prev')). t \<le> nt"
            proof -
              have
                "(\<forall>db \<in> set auxlist'. time db \<le> nt \<and> memR (args_ivl args) (nt - time db))"
                "auxlist_data_prev args nt auxlist' = (linearize data_prev')"
                using valid
                by auto
              then have "\<forall>db \<in> set (linearize data_prev'). time db \<le> nt"
                unfolding auxlist_data_prev_def
                by (metis Set.member_filter filter_set)
              then show ?thesis
                unfolding time_def ts_tuple_rel_f_def
                by auto
            qed
            ultimately have "\<forall>t \<in> fst ` ts_tuple_rel_binary_lhs (set (linearize data_prev'')). t \<le> nt"
              using ts_rel_union
              by auto
            then have "\<forall>t \<in> (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas}). t \<le> nt"
              by auto
            then have "Max (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas}) = nt"
              using nt_mem
              by (meson Max_eqI finite_nat_set_iff_bounded_le)
            then show ?thesis
              using Some t_eq non_empty
              unfolding safe_max_def
              by (auto split: if_splits)
          next
            case False
            then have "Mapping.lookup tuple_in_once'' tuple = Mapping.lookup tuple_in_once' tuple"
              using Some
              unfolding tuple_in_once''_def
              by (simp add: Mapping_lookup_upd_set)
            moreover have "fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} = fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). tuple = snd tas}"
              using False tuple_not_mem_empty ts_rel_union
              unfolding ts_tuple_rel_f_def
              by auto
            ultimately show ?thesis
              using before
              unfolding newest_tuple_in_mapping_def
              by auto
          qed
        qed
      }
      moreover {
        fix tuple::"'a option list"
        assume wf: "\<not>wf_tuple (args_n args) (args_L args) tuple"

        then have lookup: "Mapping.lookup tuple_in_once'' tuple = None"
          using table_in_once''
          unfolding table_def
          by (meson Mapping_keys_intro)

        {
          assume "{tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} \<noteq> {}"
          then obtain t l r where "tuple \<in> l" "(t, l, r) \<in> set (linearize data_prev'')"
            unfolding ts_tuple_rel_f_def
            by auto
          then have "wf_tuple (args_n args) (args_L args) tuple"
            using data_prev''_relL
            unfolding relL_def
            by auto
          then have "False"
            using wf
            by auto
        }
        then have "{tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas} = {}"
          by auto
        then have "Mapping.lookup tuple_in_once'' tuple = safe_max (fst ` {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'')). tuple = snd tas})"
          using lookup
          unfolding safe_max_def
          by auto
      }
      ultimately show ?thesis
        unfolding newest_tuple_in_mapping_def
        by auto
    qed
    moreover have "(\<forall>as \<in> Mapping.keys tuple_in_once''. case Mapping.lookup tuple_in_once'' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev'') \<and> join_cond (args_pos args) l (proj_tuple maskL as))"
    proof -
      have before: "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l (proj_tuple maskL as))"
        using valid
        by auto
      {
        fix as
        assume "as \<in> Mapping.keys tuple_in_once''"
        then obtain t where t_props: "Mapping.lookup tuple_in_once'' as = Some t"
          by (meson Mapping_keys_dest)
        have "case Mapping.lookup tuple_in_once'' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev'') \<and> join_cond (args_pos args) l (proj_tuple maskL as)"
        proof (cases "as \<in> l")
          case True
          then have t_eq: "t = nt"
            using t_props
            unfolding tuple_in_once''_def
            by (simp add: Mapping_lookup_upd_set)
          have tlr: "(nt, l, r) \<in> set (linearize data_prev'')"
            unfolding data_prev''_def append_queue_rep
            by auto
          have pos: "args_pos args"
            using valid False
            by auto
          have "proj_tuple maskL as \<in> l"
            using True proj_l
            by auto
          then have "join_cond (args_pos args) l (proj_tuple maskL as)"
            using pos
            by auto
          then show ?thesis
            using t_props tlr pos t_eq
            by auto
        next
          case False
          then have "Mapping.lookup tuple_in_once'' as = Mapping.lookup tuple_in_once' as"
            unfolding tuple_in_once''_def
            by (simp add: Mapping_lookup_upd_set)
          then have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> join_cond (args_pos args) l (proj_tuple maskL as)"
            using before t_props
            by (smt Mapping_keys_intro option.distinct(1) option.simps(5))
          then show ?thesis
            using t_props
            unfolding data_prev''_def append_queue_rep
            by auto
        qed
      }
      then show ?thesis
        by auto
    qed
    moreover have "(\<forall>as. (case Mapping.lookup tuple_since_hist' as of
      Some idx \<Rightarrow> tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx
      | None   \<Rightarrow> \<forall>idx. \<not>tuple_since_tp args as (linearize data_in') idx_oldest' idx_mid' idx)
    )"
      using valid
      by auto
    moreover have "(\<forall>tuple. tuple \<in> hist_sat' \<longleftrightarrow>
        (\<not>is_empty data_in') \<and> (
          \<forall>(t, l, r) \<in> set (auxlist_data_in args nt auxlist''). tuple \<in> r
      ))"
      unfolding auxlist_in_eq
      using valid
      by auto
    moreover have "(\<forall>tuple. tuple \<in> since_sat' \<longrightarrow>
        ((tuple \<in> hist_sat') \<or> tuple_since_lhs tuple (linearize data_in') args maskL (auxlist_data_in args nt auxlist''))
      )"
    proof -
      have "(\<forall>tuple. tuple \<in> since_sat' \<longrightarrow>
        ((tuple \<in> hist_sat') \<or> tuple_since_lhs tuple (linearize data_in') args maskL (auxlist_data_in args nt auxlist'))
      )"
        using valid
        unfolding valid_mmtaux.simps
        apply -
        apply (erule conjE)+
        apply assumption
        done
      then show ?thesis
        unfolding auxlist_in_eq
        by auto
    qed
    moreover have "(\<forall>tuple. tuple_since_lhs tuple (linearize data_in') args maskL (auxlist_data_in args nt auxlist'') \<longrightarrow>
        tuple \<in> since_sat'
      )"
      unfolding auxlist_in_eq
      using valid
      by auto
    moreover have "tuple_in_once_keys'' = Mapping.keys tuple_in_once''"
    proof -
      have "tuple_in_once_keys' = Mapping.keys tuple_in_once'"
        using valid
        by auto
      then show ?thesis
        unfolding tuple_in_once_keys''_def tuple_in_once''_def
        by (simp add: Mapping_upd_set_keys)
    qed
    moreover have "time (nt, l, r) \<le> nt"
      unfolding time_def
      by auto
    ultimately show ?thesis
      unfolding res_eq[symmetric] auxlist''_def auxlist'_def
      by (auto simp only: valid_mmtaux.simps)
  qed
qed

lemma valid_update_mmtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (args_n args) (args_L args) l \<Longrightarrow>
    table (args_n args) (args_R args) r \<Longrightarrow>
    valid_mmtaux args cur aux auxlist \<Longrightarrow>
    valid_mmtaux
      args
      nt
      (update_mmtaux args nt l r aux)
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "
  using valid_update_mmtaux_unfolded
  by (cases aux) (fast)

interpretation mmtaux: mtaux valid_mmtaux init_mmtaux update_mmtaux result_mmtaux
  using valid_init_mmtaux valid_update_mmtaux valid_result_mmtaux
  by unfold_locales

(*<*)
end
(*>*)
