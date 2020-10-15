theory Semantics
  imports SepAlgebra
begin

subsection \<open>Abstract language\<close>

datatype ('a, 'b, 'c) stmt =
  Inhale "'a assertion"
  | Assume "'a assertion"
  | Exhale "'a assertion"
  | Skip
  | Seq "('a, 'b, 'c) stmt" "('a, 'b, 'c) stmt" (infixl ";" 60)
  | If "('a, 'b, 'c) stmt" "('a, 'b, 'c) stmt"
  | Var "'b list"
  | Havoc "'b list"
  | MethodCall "'b list" "string" "'b list"
  | While "'a assertion" "'a assertion" "('a, 'b, 'c) stmt"
  | Other 'c

(* Name \<times> x \<times> y \<times> P \<times> Q \<times> s *)
type_synonym ('a, 'b, 'c) method = "string \<times> 'b list \<times> 'b list \<times> 'a assertion \<times> 'a assertion \<times> ('a, 'b, 'c) stmt"

type_synonym ('a, 'b, 'c) program = "('a, 'b, 'c) method list"

fun get_method :: "('a, 'b, 'c) program \<Rightarrow> string \<Rightarrow> ('a, 'b, 'c) method option" where
  "get_method (t # q) s = (if fst t = s then Some t else get_method q s)"
| "get_method _ s = None"

fun get_args :: "('a, 'b, 'c) method \<Rightarrow> 'b list" where
  "get_args (_, args, _, _, _, _) = args"

fun get_ret :: "('a, 'b, 'c) method \<Rightarrow> 'b list" where
  "get_ret (_, _, ret, _, _, _) = ret"

fun get_args_ret :: "('a, 'b, 'c) method \<Rightarrow> 'b list" where
  "get_args_ret m = get_args m @ get_ret m"

fun get_pre :: "('a, 'b, 'c) method \<Rightarrow> 'a assertion" where
  "get_pre (_, _, _, P, _, _) = P"

fun get_post :: "('a, 'b, 'c) method \<Rightarrow> 'a assertion" where
  "get_post (_, _, _, _, Q, _) = Q"

fun get_body :: "('a, 'b, 'c) method \<Rightarrow> ('a, 'b, 'c) stmt" where
  "get_body (_, _, _, _, _, s) = s"

datatype 'a ss = S "'a set" | Error

type_synonym 'b rename_t = "'b list \<times> 'b list \<times> 'b list \<times> 'b list"

fun get_S :: "'a ss \<Rightarrow> 'a set" where
  "get_S (S A) = A"
| "get_S _ = undefined"

fun union_set_ss :: "'a ss set \<Rightarrow> 'a ss" where
  "union_set_ss A = (if Error \<in> A then Error
    else S (\<Union>a\<in>A. get_S a))"

fun len :: "('a, 'b, 'c) stmt \<Rightarrow> nat" where
  "len (MethodCall y m x) = 5"
| "len (While b I s) = 5 + len s"
| "len (If s1 s2) = len s1 + len s2"
| "len (s1 ; s2) = len s1 + len s2"
| "len _ = 1"

lemma len_at_least_one:
  "len s \<ge> 1"
by (induct rule: len.induct) auto

definition lnot :: "'a assertion \<Rightarrow> 'a assertion" where
  "lnot P \<phi> = (if P \<phi> = None then None else Some (\<not> the (P \<phi>)))"

fun wf_renaming :: "'b rename_t \<Rightarrow> bool" where
  "wf_renaming (old_vars, new_vars, vars_to_avoid, domain) \<longleftrightarrow>
      length old_vars = length new_vars \<and> distinct old_vars \<and> distinct new_vars"

definition lfalse :: "'a assertion" where
  "lfalse = (\<lambda>s. Some False)"

definition well_defined_assert :: "'a assertion \<Rightarrow> 'a \<Rightarrow> bool" where
  "well_defined_assert P \<phi> \<longleftrightarrow> P \<phi> \<noteq> None"

locale semantics_algebra = sep_algebra +

  fixes Inh :: "'a assertion \<Rightarrow> 'a set"

  fixes semantics_other :: "('a, 'b, 'c) program \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'a ss"

  fixes read_pred :: "'a assertion \<Rightarrow> 'b list"
  fixes read_other :: "'c \<Rightarrow> 'b list"

  fixes modif_other :: "'c \<Rightarrow> 'b list"

  fixes rename_elem :: "'b \<Rightarrow> 'b rename_t \<Rightarrow> 'b"
  fixes rename_other :: "'c \<Rightarrow> 'b rename_t \<Rightarrow> 'c"
  fixes rename_state :: "'a \<Rightarrow> 'b rename_t \<Rightarrow> 'a"
  fixes rename_pred :: "'a assertion \<Rightarrow> 'b rename_t \<Rightarrow> 'a assertion"
  fixes rename_inv :: "'b rename_t \<Rightarrow> 'b rename_t"

  fixes wf_other :: "('a, 'b, 'c) program \<Rightarrow> 'c \<Rightarrow> bool"

assumes 

  (* Read assertions *)
      read_pred_def: "set (read_pred P) = (\<Union>i\<in>Inh P. \<sigma> i)"
  and can_read_not: "well_defined_assert P a \<longleftrightarrow> well_defined_assert (lnot P) a"
  and pred_read_pred_same: "C x = C y \<Longrightarrow> x << y \<Longrightarrow> (\<sigma> y - \<sigma> x) \<inter> set (read_pred P) = {} \<Longrightarrow> P y = P x"

  (* Other *)
  and modif_other_sem: "wf_other Pr other \<and> c \<in> get_S (semantics_other Pr a other) \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif_other other)"
  and modif_other_read_other: "set (modif_other other) \<subseteq> set (read_other other)"
  and no_modif_other_axiom: "semantics_other Pr \<phi>' other \<noteq> Error \<and> wf_other Pr other \<and> \<phi> << \<phi>' \<and> \<sigma> \<phi> \<inter> set (modif_other other) = {} \<Longrightarrow> get_S (semantics_other Pr \<phi>' other) >> {\<phi>}"

  (* Rename_invert *)
  and rename_inv_def_elem: "wf_renaming t \<Longrightarrow> rename_elem (rename_elem elem t) (rename_inv t) = elem"
  and rename_inv_def_other: "wf_renaming t \<Longrightarrow> rename_other (rename_other other t) (rename_inv t) = other"
  and renaming_invert_wf: "wf_renaming t \<Longrightarrow> wf_renaming (rename_inv t)"

  (* Renaming element properties *)
  and rename_removes_vars_elem: "wf_renaming (l1, l2, l3, do) \<Longrightarrow> var \<in> set do \<Longrightarrow>
            rename_elem var (l1, l2, l3, do) \<in> set l1 \<union> set l3 \<Longrightarrow> rename_elem var (l1, l2, l3, do) \<in> set l2"
  and rename_elem_in_l1_l2: "wf_renaming (l1, l2, l3, do) \<Longrightarrow> i < length l1 \<Longrightarrow> rename_elem (l1 ! i) (l1, l2, l3, do) = l2 ! i"

  (* Renaming states *)
  and rename_store: "wf_renaming t \<Longrightarrow> \<sigma> (rename_state a t) = (\<lambda>elem. rename_elem elem t) ` (\<sigma> a)"
  and rename_state_add: "wf_renaming t \<Longrightarrow> Some a = Some d \<oplus> Some c \<Longrightarrow> Some (rename_state a t) = Some (rename_state d t) \<oplus> Some (rename_state c t)"
  and rename_state_identity: "wf_renaming t \<Longrightarrow> (\<forall>x\<in>\<sigma> a. rename_elem x t = x) \<Longrightarrow> rename_state a t = a"
  and rename_state_double: "wf_renaming t \<Longrightarrow> wf_renaming t1 \<Longrightarrow> wf_renaming t2 \<Longrightarrow>
            (\<forall>x\<in>\<sigma> a. rename_elem x t = rename_elem (rename_elem x t1) t2) \<Longrightarrow> rename_state a t = rename_state (rename_state a t1) t2"

  (* Renaming assertions *)
  and rename_pred_def: "rename_pred P t = (\<lambda>\<phi>. P (rename_state \<phi> (rename_inv t)))"
  and inh_renamed: "wf_renaming t \<Longrightarrow> Inh (rename_pred P t) = rename_set (Inh P) t"

  (* Renaming other *)
  and read_other_rename_other: "read_other (rename_other other t) = map (\<lambda>elem. rename elem t) (read_other other)"
  and modif_rename_other: "modif_other (rename_other other t) = map (\<lambda>elem. rename_elem elem t) (modif_other other)"
  and wf_other_renaming: "wf_renaming t \<Longrightarrow> wf_other Pr other \<Longrightarrow> wf_other Pr (rename_other other t)"
  and ver_rename_other: "wf_renaming t \<Longrightarrow> semantics_other Pr \<phi> other \<noteq> Error  \<Longrightarrow> semantics_other Pr (rename_state \<phi> t) (rename_other other t) \<noteq> Error"
  and semantics_rename_other: "wf_renaming t \<Longrightarrow> a \<in> get_S (semantics_other Pr (rename_state \<phi> t) (rename_other other t))
                                \<Longrightarrow> rename_state a (rename_inv t) \<in> get_S (semantics_other Pr \<phi> other)"

begin

lemma finite_store:
  "finite (\<sigma> x)"
proof -
  let ?s = "{a. card (\<sigma> a) = 1 \<and> a << x \<and> pure a}"
  have "finite ?s" using finiteness[of x]
    by (metis (no_types, lifting) Collect_mono infinite_super)
  moreover have "\<And>a. a \<in> ?s \<Longrightarrow> finite (\<sigma> a)"
    using neq0_conv by fastforce
  ultimately have "finite (\<Union>a\<in>?s. \<sigma> a)" using finite_UN_I[of ?s \<sigma>] by blast
  moreover have "\<sigma> x \<subseteq> (\<Union>a\<in>?s. \<sigma> a)" (is "?a \<subseteq> ?b")
  proof (rule subsetI)
    fix var assume "var \<in> ?a"
    then obtain c where "\<sigma> c = {var}" "c << x"
      using unique_store_exists by blast
    then have "|c| \<in> ?s"
    proof -
      have "\<sigma> |c| = {var}"
        using \<open>\<sigma> c = {var}\<close> store_pure by blast
      then have "card (\<sigma> |c| ) = 1"
        using is_singleton_altdef is_singleton_def by blast
      then show ?thesis
        by (smt \<open>c << x\<close> core_properties(1) core_properties(2) mem_Collect_eq smaller_trans)
    qed
    then show "var \<in> ?b"
      by (metis (no_types, lifting) UN_I \<open>\<sigma> c = {var}\<close> insertI1 store_pure)
  qed
  ultimately show ?thesis
    using finite_subset by blast
qed

lemma rename_inv_def_state:
  assumes "wf_renaming t"
    shows "rename_state (rename_state a t) (rename_inv t) = a" (is "?a = a")
proof -
  obtain l where "set l = \<sigma> a" "distinct l"
    by (meson finite_distinct_list finite_store)
  let ?t = "(l, l, [], [])"
  have "wf_renaming ?t"
    using \<open>distinct l\<close> by auto
  moreover have "rename_state a ?t = a"
    by (metis (no_types, hide_lams) \<open>distinct l\<close> \<open>set l = \<sigma> a\<close> calculation distinct_Ex1 rename_state_identity semantics_algebra.rename_elem_in_l1_l2 semantics_algebra_axioms)
  moreover have "\<And>x. x \<in> \<sigma> a \<Longrightarrow> rename_elem (rename_elem x t) (rename_inv t) = rename_elem x ?t"
    by (metis \<open>distinct l\<close> \<open>set l = \<sigma> a\<close> assms calculation(1) distinct_Ex1 rename_elem_in_l1_l2 rename_inv_def_elem)
  ultimately show ?thesis
    by (metis assms rename_state_double renaming_invert_wf)
qed

lemma well_defined_assert_rename:
  assumes "wf_renaming t"
      and "well_defined_assert P \<phi>"
    shows "well_defined_assert (rename_pred P t) (rename_state \<phi> t)"
proof -
  have "rename_pred P t (rename_state \<phi> t) = P (rename_state (rename_state \<phi> t) (rename_inv t))"
    using rename_pred_def by auto
  then have "... = P \<phi>"
    by (simp add: assms(1) rename_inv_def_state)
  then show ?thesis 
    by (metis \<open>rename_pred P t (rename_state \<phi> t) = P (rename_state (rename_state \<phi> t) (rename_inv t))\<close> assms(2) well_defined_assert_def)
qed

definition wf_assert :: "'a assertion \<Rightarrow> bool" where
  "wf_assert P \<longleftrightarrow> (\<forall>\<phi>. (P \<phi> = Some True \<longleftrightarrow> {\<phi>} >> Inh P) \<and> (well_defined_assert P \<phi> \<longleftrightarrow> (\<forall>i \<in> Inh P. \<phi> ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> \<phi>)))"

lemma pure_is_exactly_store: "a << c \<Longrightarrow> b << c \<Longrightarrow> pure a \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> b \<Longrightarrow> a << b"
  by (metis commutative defined_trans_plus definedness(3) compatible_stores pure_smaller_ok smaller_def)

lemma rename_state_c_same:
  assumes "wf_renaming t"
  shows "C (rename_state a t) = C a"
proof -
  have "\<sigma> (C a) = {}"
    by (metis c_empty_core store_empty store_pure)
  then have "rename_state (C a) t = C a"
    by (simp add: assms rename_state_identity)
  moreover have "Some (rename_state a t) = Some (rename_state (C a) t) \<oplus> Some (rename_state |a| t)"
    by (metis assms commutative decompo rename_state_add)
  moreover have "s_C (rename_state a t) = s_C a \<oplus> s_C (rename_state |a| t)"
    using c_add calculation(1) calculation(2) properties_c(2) s_C_def by auto
  moreover have "C (rename_state |a| t) = u"
    by (metis assms core_properties(1) pure_c pure_def rename_state_add)
  ultimately show ?thesis
    by (simp add: neutral s_C_def)
qed

lemma rename_state_same:
  assumes "wf_renaming t1"
      and "wf_renaming t2"
      and "\<And>x. x \<in> \<sigma> a \<Longrightarrow> rename_elem x t1 = rename_elem x t2"
    shows "rename_state a t1 = rename_state a t2"
proof -
  obtain l where "set l = \<sigma> a" "distinct l"
    by (meson finite_distinct_list finite_store)
  let ?t = "(l, l, [], [])"
  have "wf_renaming ?t"
    using \<open>distinct l\<close> by auto
  moreover have "rename_state a ?t = a"
    by (metis (no_types, hide_lams) \<open>distinct l\<close> \<open>set l = \<sigma> a\<close> calculation distinct_Ex1 rename_state_identity semantics_algebra.rename_elem_in_l1_l2 semantics_algebra_axioms)
  moreover have "rename_state (rename_state a ?t) t1 = rename_state a t2"
  proof -
    have "\<And>x. x \<in> \<sigma> a \<Longrightarrow> rename_elem (rename_elem x ?t) t1 = rename_elem x t2"
      by (metis \<open>set l = \<sigma> a\<close> assms(3) calculation(1) in_set_conv_nth rename_elem_in_l1_l2)
    then show ?thesis
      by (metis assms(1) assms(2) calculation(1) rename_state_double)
  qed
  ultimately show ?thesis by simp
qed

lemma rename_store_same_if_l1:
  assumes "wf_renaming (l1, l2, l3, do)"
      and "\<sigma> a \<subseteq> set l1"
    shows "rename_state a (l1, l2, l3, do) = rename_state a  (l1, l2, [], d)"
proof -
  let ?t = "(l1, l2, l3, do)"
  let ?t' = "(l1, l2, [], d)"
  have "wf_renaming ?t'"
    using assms(1) by auto
  moreover have "\<And>x. x \<in> \<sigma> a \<Longrightarrow> rename_elem x ?t = rename_elem x ?t'"
    by (metis (no_types, lifting) assms(1) assms(2) calculation in_mono in_set_conv_nth rename_elem_in_l1_l2)
  ultimately show ?thesis
    by (simp add: rename_state_same)
qed

definition read_mono :: "'a assertion \<Rightarrow> bool" where
  "read_mono P \<longleftrightarrow> (\<forall>\<phi> \<phi>'. \<phi> << \<phi>' \<longrightarrow> well_defined_assert P \<phi> \<longrightarrow> well_defined_assert P \<phi>')"

lemma can_read_false:
  "well_defined_assert lfalse a"
  by (simp add: lfalse_def well_defined_assert_def)

fun rename_set :: "'a set \<Rightarrow> 'b rename_t \<Rightarrow> 'a set" where
  "rename_set A t = (\<lambda>\<phi>. rename_state \<phi> t) ` A"

lemma rename_pred_same: 
  assumes "wf_renaming t"
  shows "P \<phi> = Some b \<longleftrightarrow> (rename_pred P t) (rename_state \<phi> t) = Some b"
  by (simp add: assms rename_inv_def_state rename_pred_def)

lemma wf_renaming_order:
  assumes "wf_renaming t"
    and "a << b"
  shows "rename_state a t << rename_state b t"
  using assms(1) assms(2) rename_state_add smaller_def by blast

lemma wf_renaming_diff:
  assumes "wf_renaming t"
    and "a \<noteq> b"
  shows "rename_state a t \<noteq> rename_state b t"
  by (metis assms(1) assms(2) rename_inv_def_state)

lemma read_pred_rename_pred:
  assumes "wf_renaming t"
  shows "set (read_pred (rename_pred P t)) = (\<lambda>elem. rename_elem elem t) ` (set (read_pred P))" (is "?a = ?b")
proof -
  let ?r = "(\<lambda>elem. rename_elem elem t)"
  let ?P = "rename_pred P t"
  have "?a = (\<Union>i\<in>Inh ?P. \<sigma> i)"
    by (simp add: read_pred_def)
  moreover have "Inh ?P = rename_set (Inh P) t"
    using assms inh_renamed by blast
  moreover have "set (read_pred P) = (\<Union>i\<in>Inh P. \<sigma> i)"
    using read_pred_def by blast
  moreover have "?b = (\<Union>i\<in>Inh P. ?r ` (\<sigma> i))"
    by (simp add: image_UN read_pred_def)
  moreover have "?a = (\<Union>i\<in>Inh P. \<sigma> (rename_state i t))"
    using calculation(1) calculation(2) by auto
  moreover have "\<And>i. \<sigma> (rename_state i t) = ?r ` (\<sigma> i)"
    using rename_store assms by auto
  ultimately show ?thesis
    by auto
qed

lemma wf_rename_inv_other:
  assumes "wf_renaming t"
  shows "rename_state (rename_state x (rename_inv t)) t = x"
  by (meson assms semantics_algebra.rename_inv_def_state semantics_algebra.renaming_invert_wf semantics_algebra.wf_renaming_diff semantics_algebra_axioms)

definition rename_list :: "'b list \<Rightarrow> 'b rename_t \<Rightarrow> 'b list" where
  "rename_list l t = map (\<lambda>elem. rename_elem elem t) l"

lemma rename_state_neutral:
  assumes "wf_renaming t"
  shows "rename_state u t = u" (is "?r = u")
proof -
  have "C ?r = u"
    by (simp add: assms neutral_parts(2) rename_state_c_same)
  moreover have "\<sigma> ?r = {}"
    using rename_store store_empty assms by auto
  ultimately show ?thesis
    by (metis core_properties(1) assms pure_u rename_state_c_same semantics_algebra.pure_is_exactly_store semantics_algebra_axioms sep_algebra.antisym sep_algebra.properties_c(1) sep_algebra_axioms set_eq_subset smaller_refl store_empty store_pure u_smaller)
qed

lemma rename_removes_vars_other:
  assumes "wf_renaming (l1, l2, l3, do)"
      and "set (read_other other) \<subseteq> set do"
    shows "set (read_other (rename_other other (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3) \<subseteq> set l2" (is "?a \<subseteq> ?b")
proof (rule subsetI)
  let ?t = "(l1, l2, l3, do)"
  fix x assume "x \<in> ?a"
  then obtain y where "y \<in> set (read_other other)" "x = rename_elem y ?t"
    using read_other_rename_other[of other ?t]
    by (smt IntE image_iff set_map)
  then show "x \<in> ?b"
    using \<open>x \<in> set (read_other (rename_other other (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3)\<close> assms(1) assms(2) rename_removes_vars_elem by auto
qed

lemma rename_removes_vars_other_modif:
  assumes "wf_renaming (l1, l2, l3, do)"
      and "set (modif_other other) \<subseteq> set do"
    shows "set (modif_other (rename_other other (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3) \<subseteq> set l2" (is "?a \<subseteq> ?b")
proof (rule subsetI)
  let ?t = "(l1, l2, l3, do)"
  fix x assume "x \<in> ?a"
  then obtain y where "y \<in> set (modif_other other)" "x = rename_elem y ?t"
    using modif_rename_other[of other ?t]
    by (smt IntE image_iff set_map)
  then show "x \<in> ?b"
    using \<open>x \<in> set (modif_other (rename_other other (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3)\<close> assms(1) assms(2) rename_removes_vars_elem by auto
qed

lemma pure_is_exactly_store_variant: 
  assumes "a << b"
      and "pure b"
      and "\<sigma> a = \<sigma> b"
    shows "a = b"
proof -
  obtain c where "Some c = Some a \<oplus> Some b"
    by (metis assms(1) assms(2) commutative_monoid.commutative commutative_monoid_axioms pure_smaller_ok smaller_pure)
  then have "b << a" using pure_is_exactly_store[of b c a] using assms
    by (metis commutative option.sel pure_smaller_ok smaller_pure smaller_refl subset_refl)
  then show ?thesis
    by (simp add: assms(1) local.antisym)
qed

definition h :: "'b list \<Rightarrow> 'a set" where
  "h V = {\<phi>. pure \<phi> \<and> \<sigma> \<phi> = set V}"

lemma h_store:
  assumes "\<phi> \<in> h l"
  shows "\<sigma> \<phi> = set l"
  using assms h_def by blast

lemma h_pure:
  assumes "hx \<in> h x"
  shows "pure hx"
  using assms h_def by blast

lemma all_stores_exist:
  "s \<subseteq> \<sigma> a  \<Longrightarrow> \<exists>c. c << a \<and> \<sigma> c = s"
proof (induction "card s" arbitrary: s)
  case 0
  show ?case
    by (metis "0.hyps" "0.prems" card_eq_0_iff finite_store rev_finite_subset store_empty u_smaller)
next
  case (Suc n)
  obtain var where "var \<in> s"
    using Suc.hyps(2) by fastforce
  let ?s = "s - {var}"
  have "card ?s = n"
    by (metis Diff_empty Suc.hyps(2) \<open>var \<in> s\<close> card_Diff_insert card_ge_0_finite diff_Suc_1 empty_iff zero_less_Suc)
  then obtain c where "c << a \<and> \<sigma> c = ?s"
    using Suc.hyps(1) Suc.prems by blast
  moreover obtain d where "d << a \<and> \<sigma> d = {var}"
    by (meson Suc.prems \<open>var \<in> s\<close> subsetD unique_store_exists)
  ultimately have "|c| ## |d|"
    using core_properties(1) defined_disjoint_store store_pure by auto
  then obtain e where e_def: "Some e = s_core c \<oplus> s_core d"
    by (metis Option.is_none_def option.exhaust_sel commutative_monoid.defined_def commutative_monoid_axioms s_core_def)
  then have "e << a"
  proof -
    obtain "|c| << a" "|d| << a"
      using \<open>c << a \<and> \<sigma> c = s - {var}\<close> \<open>d << a \<and> \<sigma> d = {var}\<close> core_properties(2) smaller_trans by blast
    then show ?thesis
      by (smt \<open>Some e = s_core c \<oplus> s_core d\<close> core_properties(1) pure_smaller_ok s_core_def sep_algebra.add_trans sep_algebra_axioms smaller_refl)
  qed
  moreover have "\<sigma> e = \<sigma> c \<union> \<sigma> d" using e_def
    using s_core_def store_add store_pure by auto
  ultimately show ?case
    using \<open>c << a \<and> \<sigma> c = s - {var}\<close> \<open>d << a \<and> \<sigma> d = {var}\<close> \<open>var \<in> s\<close> by auto
qed

lemma h_bigger:
  assumes "set x \<subseteq> \<sigma> \<phi>"
  shows "{\<phi>} >> h x"
proof -
  obtain a where "a << \<phi>" "\<sigma> a = set x"
    using all_stores_exist assms by blast
  then have "|a| \<in> h x"
    using core_properties(1) h_def store_pure by auto
  then show ?thesis
    by (metis \<open>a << \<phi>\<close> core_properties(2) commutative_monoid.smaller_trans commutative_monoid_axioms sep_algebra.bigger_set_def sep_algebra_axioms singletonD)
qed

lemma h_lin_simpler:
  assumes "set v = set v1 \<union> set v2"
      and "set v1 \<inter> set v2 = {}"
  shows "h v = h v1 \<oplus>\<oplus> h v2" (is "?a = ?b")
proof -
  have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix x assume "x \<in> ?b"
    then obtain x1 x2 where "x1 \<in> h v1" "x2 \<in> h v2" "Some x = Some x1 \<oplus> Some x2"
      using set_add_elem by blast
    then show "x \<in> ?a"
      by (metis (mono_tags, lifting) assms(1) h_def mem_Collect_eq store_add sum_pure)
  qed
  moreover have "?a \<subseteq> ?b"
  proof (rule subsetI)
    fix x assume "x \<in> ?a"
    then obtain "set v1 \<subseteq> \<sigma> x" "set v2 \<subseteq> \<sigma> x"
      by (simp add: assms h_store)
    then obtain "{x} >> h v1" "{x} >> h v2"
      by (simp add: h_bigger)
    then obtain x1 x2 where "x1 \<in> h v1" "x2 \<in> h v2" "x1 << x" "x2 << x"
      using bigger_set_def by auto
    then obtain xx where "Some xx = Some x1 \<oplus> Some x2" using defined_disjoint_store[of x1 x2] assms
      by (metis Option.is_none_def defined_def h_pure h_store option.collapse)
    then have "x = xx"
    proof -
      have "xx << x"
        using \<open>Some xx = Some x1 \<oplus> Some x2\<close> \<open>x1 << x\<close> \<open>x2 << x\<close> \<open>x2 \<in> h v2\<close> add_trans h_pure pure_smaller_ok smaller_refl by blast
      moreover have "pure x"
        using \<open>x \<in> h v\<close> h_pure by blast
      moreover have "\<sigma> xx = \<sigma> x"
        using \<open>Some xx = Some x1 \<oplus> Some x2\<close> \<open>x \<in> h v\<close> \<open>x1 \<in> h v1\<close> \<open>x2 \<in> h v2\<close> assms(1) h_store store_add by auto
      ultimately show ?thesis 
        using pure_is_exactly_store_variant by auto
    qed
    then show "x \<in> ?b"
      using \<open>Some xx = Some x1 \<oplus> Some x2\<close> \<open>x1 \<in> h v1\<close> \<open>x2 \<in> h v2\<close> set_add_elem_reci by blast
  qed
  ultimately show ?thesis by blast
qed

lemma h_v_add:
  "h v = h v \<oplus>\<oplus> h v" (is "?a = ?b")
proof -
  have "?a \<subseteq> ?b"
    using h_pure pure_def sep_algebra.set_add_elem_reci sep_algebra_axioms by fastforce
  moreover have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix x assume "x \<in> ?b"
    obtain a b where "a \<in> h v" "b \<in> h v" "Some x = Some a \<oplus> Some b"
      using \<open>x \<in> h v \<oplus>\<oplus> h v\<close> set_add_elem by blast
    then show "x \<in> ?a"
      by (metis Un_absorb h_pure h_store pure_is_exactly_store_variant smaller_def store_add sum_pure)
  qed
  ultimately show ?thesis by blast
qed

lemma exists_list_inter:
  "\<And>b. \<exists>c. set c = set a \<inter> set b"
proof (induction a)
  case Nil
  then show ?case by simp
next
  case (Cons a1 a2)
  then show ?case
    by (meson List.finite_set finite_Int finite_distinct_list)
qed

lemma exists_list_minus:
  "\<And>b. \<exists>c. set c = set a - set b"
proof (induction a)
  case Nil
  then show ?case by simp
next
  case (Cons a1 a2)
  then show ?case
    by (simp add: finite_list)
qed

lemma h_lin:
  assumes "set v = set v1 \<union> set v2"
  shows "h v = h v1 \<oplus>\<oplus> h v2" (is "?a = ?b")
proof -
  obtain inter where "set inter = set v1 \<inter> set v2"
    by (meson exists_list_inter)
  then obtain v1' v2' where "set v1' = set v1 - set inter" "set v2' = set v2 - set inter"
    by (meson exists_list_minus)
  then obtain "h v1 = h v1' \<oplus>\<oplus> h inter" "h v2 = h v2' \<oplus>\<oplus> h inter"
    using \<open>set inter = set v1 \<inter> set v2\<close> h_lin_simpler inf.commute
    by (metis Diff_Diff_Int Diff_eq_empty_iff Diff_idemp Un_Diff_Int Un_upper2)
  moreover obtain v_union where "set v_union = set v1' \<union> set v2'"
    by (meson set_append)
  ultimately have "h v_union = h v1' \<oplus>\<oplus> h v2'"
    by (metis Diff_Diff_Int Int_Diff Int_lower2 Un_Diff_Int Un_Diff_cancel \<open>set inter = set v1 \<inter> set v2\<close> \<open>set v1' = set v1 - set inter\<close> \<open>set v2' = set v2 - set inter\<close> empty_iff h_lin_simpler subsetI subset_antisym)
  moreover have "set v = set v_union \<union> set inter"
    using \<open>set inter = set v1 \<inter> set v2\<close> \<open>set v1' = set v1 - set inter\<close> \<open>set v2' = set v2 - set inter\<close> \<open>set v_union = set v1' \<union> set v2'\<close> assms by auto
  ultimately have "h v = h v_union \<oplus>\<oplus> h inter"
    by (metis Diff_Diff_Int Diff_eq_empty_iff Diff_idemp Un_Diff \<open>set v1' = set v1 - set inter\<close> \<open>set v2' = set v2 - set inter\<close> \<open>set v_union = set v1' \<union> set v2'\<close> h_lin_simpler order_refl)
  then have "h v = h v1' \<oplus>\<oplus> h v2' \<oplus>\<oplus> h inter"
    by (simp add: \<open>h v_union = h v1' \<oplus>\<oplus> h v2'\<close>)
  moreover have "h inter \<oplus>\<oplus> h inter = h inter"
    using h_v_add by auto
  ultimately show ?thesis
    by (metis \<open>\<And>thesis. (\<lbrakk>h v1 = h v1' \<oplus>\<oplus> h inter; h v2 = h v2' \<oplus>\<oplus> h inter\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> set_add_asso simple_set_add_comm)
qed

fun h_comp_some :: "'a \<Rightarrow> 'b list \<Rightarrow> 'a" where
  "h_comp_some a l = (THE b. b << a \<and> \<sigma> b = \<sigma> a - set l \<and> pure b)"

lemma h_comp_some_exists:
  assumes "b = h_comp_some a l"
  shows "b << a \<and> \<sigma> b = \<sigma> a - set l \<and> pure b"
proof -
  define P where "P = (\<lambda>y. y << a \<and> \<sigma> y = \<sigma> a - set l \<and> pure y)"
  obtain b' where "b' << a \<and> \<sigma> b' = \<sigma> a - set l"
    using all_stores_exist by fastforce
  then have "P |b'|"
    by (metis P_def core_properties(1) core_properties(2) smaller_trans store_pure)
  moreover have "\<And>y. P y \<Longrightarrow> y = |b'|"
  proof -
    fix y assume "P y"
    then have "\<sigma> y = \<sigma> |b'|"
      using P_def calculation by blast
    thm pure_is_exactly_store[of ]
    then show "y = |b'|"
      by (smt Int_absorb Int_lower1 P_def \<open>P y\<close> \<open>b' << a \<and> \<sigma> b' = \<sigma> a - set l\<close> calculation core_properties(1) pure_is_exactly_store pure_is_exactly_store_variant)
  qed
  ultimately have "P (THE y. P y)" using theI[of P "|b'|"] by blast
  then show ?thesis using P_def assms by simp
qed

definition h_comp :: "'a \<Rightarrow> 'b list \<Rightarrow> 'a" where
  "h_comp \<phi> V = (the (s_C \<phi> \<oplus> Some (h_comp_some \<phi> V)))"

lemma h_comp_some_sum:
  "Some (h_comp \<phi> V) = s_C \<phi> \<oplus> Some (h_comp_some \<phi> V)"
proof -
  have "s_C \<phi> \<oplus> Some (h_comp_some \<phi> V) \<noteq> None"
    by (metis associative defined_def definedness(1) h_comp_some_exists is_none_code(1) is_none_code(2) partially_cancellative plus.simps(2) pure_def s_C_def smaller_def)
  then show ?thesis
    by (simp add: h_comp_def)
qed

lemma h_comp_store:
  "\<sigma> (h_comp \<phi> l) = \<sigma> \<phi> - set l"
proof -
  have "\<sigma> (h_comp \<phi> l) = \<sigma> (C \<phi>) \<union> \<sigma> (h_comp_some \<phi> l)"
    by (metis s_C_def h_comp_some_sum store_add)
  then show ?thesis
    by (metis Un_commute Un_empty_right c_empty_core h_comp_some_exists store_empty store_pure)
qed

lemma h_comp_grows:
  assumes "c << a"
  shows "h_comp c V << h_comp a V"
proof -
  have "h_comp_some c V << h_comp_some a V" (is "?c << ?a")
  proof -
    have "\<sigma> ?c \<subseteq> \<sigma> ?a"
    proof -
      have "\<sigma> c \<subseteq> \<sigma> a" using assms(1) store_add smaller_def 
        by auto
      then show ?thesis 
        by (metis DiffE DiffI UnCI h_comp_some_exists subsetI sup.order_iff)
    qed
    then show "?c << ?a"
      by (meson assms h_comp_some_exists pure_is_exactly_store smaller_trans)
  qed
  then show ?thesis
    by (smt assms h_comp_some_sum s_C_def sep_algebra.add_trans sep_algebra_axioms smaller_core_comp)
qed

lemma h_comp_lin:
  assumes "Some a = Some a1 \<oplus> Some a2"
  shows "Some (h_comp a V) = Some (h_comp a1 V) \<oplus> Some (h_comp a2 V)"
proof -
  have "Some (h_comp_some a V) = Some (h_comp_some a1 V) \<oplus> Some (h_comp_some a2 V)" (is "Some ?a = Some ?a1 \<oplus> Some ?a2")
  proof -
    obtain "?a << a \<and> \<sigma> ?a = \<sigma> a - set V \<and> pure ?a"
           "?a1 << a1 \<and> \<sigma> ?a1 = \<sigma> a1 - set V \<and> pure ?a1"
           "?a2 << a2 \<and> \<sigma> ?a2 = \<sigma> a2 - set V \<and> pure ?a2"
      using h_comp_some_exists by blast
    obtain aa where "Some aa = Some ?a1 \<oplus> Some ?a2"
    proof -
      assume a1: "\<And>aa. Some aa = Some (h_comp_some a1 V) \<oplus> Some (h_comp_some a2 V) \<Longrightarrow> thesis"
      have f2: "Some a2 \<oplus> Some (h_comp_some a2 V) = Some a2"
        by (metis (no_types) \<open>\<And>thesis. (\<lbrakk>h_comp_some a V << a \<and> \<sigma> (h_comp_some a V) = \<sigma> a - set V \<and> pure (h_comp_some a V); h_comp_some a1 V << a1 \<and> \<sigma> (h_comp_some a1 V) = \<sigma> a1 - set V \<and> pure (h_comp_some a1 V); h_comp_some a2 V << a2 \<and> \<sigma> (h_comp_some a2 V) = \<sigma> a2 - set V \<and> pure (h_comp_some a2 V)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> pure_smaller_ok)
      { assume "\<exists>z. Some a2 \<oplus> (z \<oplus> Some (h_comp_some a1 V)) \<noteq> None"
        then have "(\<exists>z. None \<oplus> z \<noteq> None) \<or> (\<exists>z. Some (h_comp_some a1 V) \<oplus> Some (h_comp_some a2 V) \<noteq> None \<and> (z::'a option) \<noteq> None)"
          using f2 by (metis associative commutative)
        then have "(\<exists>a. Some (a::'a) = None) \<or> (\<exists>z. Some (h_comp_some a1 V) \<oplus> Some (h_comp_some a2 V) \<noteq> None \<and> (z::'a option) \<noteq> None)"
          by simp }
      then show ?thesis
        using a1 by (metis (no_types) \<open>\<And>thesis. (\<lbrakk>h_comp_some a V << a \<and> \<sigma> (h_comp_some a V) = \<sigma> a - set V \<and> pure (h_comp_some a V); h_comp_some a1 V << a1 \<and> \<sigma> (h_comp_some a1 V) = \<sigma> a1 - set V \<and> pure (h_comp_some a1 V); h_comp_some a2 V << a2 \<and> \<sigma> (h_comp_some a2 V) = \<sigma> a2 - set V \<and> pure (h_comp_some a2 V)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms commutative plus.elims pure_smaller_ok)
    qed
    then have "\<sigma> aa = \<sigma> ?a"
      using \<open>h_comp_some a V << a \<and> \<sigma> (h_comp_some a V) = \<sigma> a - set V \<and> pure (h_comp_some a V)\<close> \<open>h_comp_some a1 V << a1 \<and> \<sigma> (h_comp_some a1 V) = \<sigma> a1 - set V \<and> pure (h_comp_some a1 V)\<close> \<open>h_comp_some a2 V << a2 \<and> \<sigma> (h_comp_some a2 V) = \<sigma> a2 - set V \<and> pure (h_comp_some a2 V)\<close> assms store_add by auto
    then have "aa = ?a"
      by (smt \<open>Some aa = Some (h_comp_some a1 V) \<oplus> Some (h_comp_some a2 V)\<close> add_trans assms h_comp_some_exists order_refl pure_is_exactly_store pure_is_exactly_store_variant sum_pure)
    then show "Some ?a = Some ?a1 \<oplus> Some ?a2"
      using \<open>Some aa = Some (h_comp_some a1 V) \<oplus> Some (h_comp_some a2 V)\<close> by blast
  qed
  then show ?thesis
    by (metis assms associative c_add commutative h_comp_some_sum)
qed

lemma h_comp_not_here:
  assumes "set V \<inter> \<sigma> a = {}"
  shows "h_comp a V = a"
proof -
  have "h_comp_some a V = |a|"
    by (metis Diff_triv Int_commute assms core_properties(1) core_properties(3) h_comp_some_exists pure_is_exactly_store_variant smaller_core_comp store_pure)
  then show ?thesis
    by (metis commutative decompo h_comp_some_sum option.sel s_C_def)
qed

lemma h_comp_sum:
  "Some \<phi> = Some (h_comp \<phi> x) \<oplus> s_core \<phi>"
  by (smt commutative decompo h_comp_some_exists associative commutative_monoid_axioms pure_smaller_ok s_core_def h_comp_some_sum semantics_algebra_axioms s_C_def sep_algebra_axioms)

lemma h_comp_h:
  assumes "\<phi> \<in> h V"
  shows "h_comp \<phi> V = u"
  by (metis Diff_cancel assms h_comp_some_exists h_pure h_store local.antisym option.sel orig_neutral plus.simps(1) pure_c pure_is_exactly_store s_C_def semantics_algebra.h_comp_def semantics_algebra_axioms set_eq_subset store_empty u_smaller)

thm pred_read_pred_same

lemma h_comp_same_C:
  "C x = C (h_comp x V)"
proof -
  obtain y where "Some y = s_C x \<oplus> Some (h_comp_some x V)" 
    using h_comp_some_sum by blast
  then have "y = h_comp x V" 
    by (metis h_comp_def option.sel)
  then show ?thesis
    by (metis \<open>Some y = s_C x \<oplus> Some (h_comp_some x V)\<close> c_add c_empty_core commutative h_comp_some_exists neutral pure_c s_C_def unique_c)
qed

lemma no_modif_other:
  assumes "semantics_other Pr \<phi> other \<noteq> Error \<and> wf_other Pr other"
  shows "get_S (semantics_other Pr \<phi> other) >> {h_comp |\<phi>| (modif_other other)}"
proof (rule no_modif_other_axiom)
  show "semantics_other Pr \<phi> other \<noteq> Error \<and> wf_other Pr other \<and> h_comp |\<phi>| (modif_other other) << \<phi> \<and> \<sigma> (h_comp |\<phi>| (modif_other other)) \<inter> set (modif_other other) = {}"
    by (metis Diff_disjoint Int_commute assms commutative core_properties(1) h_comp_def h_comp_same_C h_comp_some_exists neutral option.sel pure_c s_C_def sep_algebra.not_pure_core sep_algebra_axioms smaller_core_comp)
qed

lemma read_pred_h_comp:
  assumes "set V \<inter> set (read_pred P) = {}"
  shows "P x = P (h_comp x V)"
proof (rule pred_read_pred_same[of "h_comp x V" x P])
  show "C (h_comp x V) = C x" 
    using h_comp_same_C by auto
  show "h_comp x V << x" 
    using h_comp_sum commutative_monoid.s_core_def commutative_monoid_axioms smaller_def by fastforce
  show "(\<sigma> x - \<sigma> (h_comp x V)) \<inter> set (read_pred P) = {}" 
    using assms h_comp_store by auto
qed

lemma rename_pure_stays_pure:
  assumes "wf_renaming t"
      and "pure x"
    shows "pure (rename_state x t)" 
  using assms(1) assms(2) pure_c rename_state_c_same by auto

lemma h_comp_some_something_inner:
  assumes "h1 << x1 \<and> \<sigma> h1 = \<sigma> x1 - set V1 \<and> pure h1"
      and "h2 << x2 \<and> \<sigma> h2 = \<sigma> x2 - set V2 \<and> pure h2"
      and "V1 = rename_list V2 t"
      and "wf_renaming t"
      and "x1 = rename_state x2 t"
    shows "h1 = rename_state h2 t" (is "h1 = ?h2")
proof -
  have "\<sigma> h1 = \<sigma> ?h2"
  proof -
    let ?f = "(\<lambda>xx. rename_elem xx t)"
    have "\<sigma> ?h2 = ?f ` (\<sigma> x2 - set V2)"
      by (simp add: assms(2) assms(4) rename_store)
    then have "... = \<sigma> x1 - set V1" (is "?a = ?b")
    proof -
      have "?b \<subseteq> ?a" 
        by (simp add: assms(3) assms(4) assms(5) image_diff_subset rename_list_def rename_store)
      moreover have "?a \<subseteq> ?b"
      proof (rule subsetI)
        fix x assume "x \<in> (\<lambda>xx. rename_elem xx t) ` (\<sigma> x2 - set V2)"
        then obtain xx where "xx \<in> \<sigma> x2 - set V2" "x = rename_elem xx t" by blast
        then have "x \<in> \<sigma> x1" 
          by (simp add: assms(4) assms(5) rename_store)
        moreover have "x \<notin> set V1"
        proof (rule ccontr)
          assume "\<not> x \<notin> set V1"
          then have "x \<in> set V1" by simp
          then obtain y where "y \<in> set V2" "x = rename_elem y t" 
            using assms(3) rename_list_def by auto
          then have "rename_elem x (rename_inv t) \<in> set V2" 
            by (simp add: assms(4) rename_inv_def_elem)
          then show "False"
            by (metis DiffD2 \<open>\<And>thesis. (\<And>xx. \<lbrakk>xx \<in> \<sigma> x2 - set V2; x = rename_elem xx t\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(4) semantics_algebra.rename_inv_def_elem semantics_algebra_axioms)
        qed
        ultimately show "x \<in> \<sigma> x1 - set V1" by simp
      qed
      ultimately show ?thesis 
        by simp
    qed
    then show ?thesis 
      by (simp add: \<open>\<sigma> (rename_state h2 t) = (\<lambda>xx. rename_elem xx t) ` (\<sigma> x2 - set V2)\<close> assms(1))
  qed
  moreover have "h1 ## ?h2"
  proof -
    have "?h2 << x1"
      by (simp add: assms(2) assms(4) assms(5) wf_renaming_order)
    moreover have "pure ?h2" using rename_pure_stays_pure assms by simp
    ultimately have "Some x1 = Some x1 \<oplus> Some ?h2" using pure_smaller_ok by blast
    then have "Some x1 = Some x1 \<oplus> Some ?h2 \<oplus> Some h1" using pure_smaller_ok assms(1) by metis
    then have "Some x1 = Some x1 \<oplus> (Some ?h2 \<oplus> Some h1)" using associative by metis
    then have "Some ?h2 \<oplus> Some h1 \<noteq> None" 
      by (metis option.simps(3) plus.simps(3))
    then have "Some h1 \<oplus> Some ?h2 \<noteq> None"  using commutative by simp
    then show ?thesis using defined_def by auto
  qed
  ultimately show ?thesis 
    by (metis assms(1) assms(2) assms(4) compatible_stores pure_c pure_is_exactly_store_variant rename_state_c_same subsetI)
qed

lemma h_comp_some_something:
  assumes "wf_renaming t"
  shows "h_comp_some (rename_state x t) (rename_list V t) = rename_state (h_comp_some x V) t"
proof -
  let ?x = "rename_state x t"
  let ?V = "rename_list V t"
  obtain h1 where "h1 << ?x \<and> \<sigma> h1 = \<sigma> ?x - set ?V \<and> pure h1" 
    using h_comp_some_exists by blast
  moreover obtain h2 where "h2 << x \<and> \<sigma> h2 = \<sigma> x - set V \<and> pure h1" 
    using calculation h_comp_some_exists by blast
  ultimately show ?thesis 
    by (meson assms h_comp_some_exists h_comp_some_something_inner)
qed

lemma rename_h_comp:
  assumes "wf_renaming t"
  shows "rename_state (h_comp x V) t = h_comp (rename_state x t) (rename_list V t)" (is "?a = ?b")
proof -
  have "C ?a = C ?b" 
    using assms h_comp_same_C rename_state_c_same by auto
  moreover have "h_comp_some (rename_state x t) (rename_list V t) = rename_state (h_comp_some x V) t" 
    using assms h_comp_some_something by blast
  moreover obtain a where "Some a = s_C x \<oplus> Some (h_comp_some x V)" 
    using h_comp_some_sum by blast
  then have "?a = rename_state a t" 
    by (metis h_comp_def option.sel)
  moreover obtain b where "Some b = s_C (rename_state x t) \<oplus> Some (h_comp_some (rename_state x t) (rename_list V t))" 
    using h_comp_some_sum by blast
  ultimately have "b = rename_state a t"
  proof -
    have "C b = C (rename_state a t)" 
      by (metis \<open>C (rename_state (h_comp x V) t) = C (h_comp (rename_state x t) (rename_list V t))\<close> \<open>Some b = s_C (rename_state x t) \<oplus> Some (h_comp_some (rename_state x t) (rename_list V t))\<close> \<open>rename_state (h_comp x V) t = rename_state a t\<close> h_comp_def option.sel)
    moreover have "|b| = |rename_state a t|"
    proof -
      have "|b| = |h_comp_some (rename_state x t) (rename_list V t)|" 
        by (metis \<open>C (rename_state (h_comp x V) t) = C (h_comp (rename_state x t) (rename_list V t))\<close> \<open>Some b = s_C (rename_state x t) \<oplus> Some (h_comp_some (rename_state x t) (rename_list V t))\<close> \<open>rename_state (h_comp x V) t = rename_state a t\<close> calculation commutative decompo_new_plus h_comp_same_C h_comp_some_exists not_pure_core partially_cancellative s_C_def s_core_def)
      moreover have "|rename_state a t| = |rename_state (h_comp_some x V) t|"
      proof -
        have "Some (rename_state a t) = Some (rename_state (C x) t) \<oplus> Some (rename_state (h_comp_some x V) t)" 
          using \<open>Some a = s_C x \<oplus> Some (h_comp_some x V)\<close> assms rename_state_add s_C_def by auto
        moreover have "|rename_state (C x) t| = u"
          by (metis assms c_empty_core empty_iff rename_state_identity store_empty store_pure)
        ultimately show ?thesis
          by (metis commutative core_add neutral option.inject commutative_monoid.s_core_def commutative_monoid_axioms)
      qed
      ultimately show ?thesis 
        using \<open>h_comp_some (rename_state x t) (rename_list V t) = rename_state (h_comp_some x V) t\<close> by auto
    qed
    ultimately show ?thesis 
      using properties_c(1) by blast
  qed
  then show ?thesis 
    by (metis \<open>Some b = s_C (rename_state x t) \<oplus> Some (h_comp_some (rename_state x t) (rename_list V t))\<close> \<open>rename_state (h_comp x V) t = rename_state a t\<close> h_comp_def option.sel)
qed

lemma wf_renaming_in_old:
  assumes "wf_renaming (l1, l2, l3, do)"
      and "x \<in> set l1"
    shows "rename_elem x (l1, l2, l3, do) \<in> set l2"
  by (metis assms(1) assms(2) in_set_conv_nth rename_elem_in_l1_l2 wf_renaming.simps)

lemma wf_renaming_inv_in_new:
  assumes "wf_renaming (l1, l2, l3, do)"
      and "x = l2 ! i"
      and "i < length l2"
    shows "rename_elem x (rename_inv (l1, l2, l3, do)) = l1 ! i"  
  by (metis assms(1) assms(2) assms(3) rename_elem_in_l1_l2 rename_inv_def_elem wf_renaming.simps)

lemma rename_pred_comp_simple:
  assumes "wf_renaming t"
      and "wf_renaming (l1, l2, [], do)"
      and "set (read_pred P) \<subseteq> set l1"
      and "wf_assert P"
    shows "rename_pred P (l1, rename_list l2 t, [], do) = rename_pred (rename_pred P (l1, l2, [], do)) t" (is "?ra = ?rb")
proof (rule ext)
  fix x
  let ?t = "(l1, l2, [], do)"
  let ?x1 = "rename_state x (rename_inv (l1, rename_list l2 t, [], do))"
  let ?x2 = "rename_state (rename_state x (rename_inv t)) (rename_inv ?t)"
  let ?t2 = "rename_inv (l1, l2, [], do)"
  let ?t1 = "rename_inv t"

  have "length l1 = length l2"
    using assms(2) wf_renaming.simps by blast
  then have "wf_renaming (l1, rename_list l2 t, [], do)"
  proof -
    have "distinct (rename_list l2 t)"
    proof -
      have "distinct l2" 
        using assms(2) wf_renaming.simps by blast
      then show ?thesis
        by (smt assms(1) distinct_conv_nth length_map nth_map rename_inv_def_elem semantics_algebra.rename_list_def semantics_algebra_axioms)
    qed
    then show ?thesis
      using assms(2) rename_list_def by auto
  qed
  have "?ra x = P (rename_state x (rename_inv (l1, rename_list l2 t, [], do)))"
    by (simp add: rename_pred_def)
  moreover have "?rb x = (rename_pred P ?t) (rename_state x (rename_inv t))"
    by (simp add: rename_pred_def)
  then have "... = P (rename_state (rename_state x (rename_inv t)) (rename_inv ?t))"
    by (simp add: rename_pred_def)
  moreover have "{?x1} >> Inh P \<longleftrightarrow> {?x2} >> Inh P" (is "?a \<longleftrightarrow> ?b")
  proof -
    have "?a \<Longrightarrow> ?b"
    proof -
      assume "?a"
      then obtain i where "i \<in> Inh P" "i << ?x1"
        using bigger_set_def by auto
      then have "\<sigma> i \<subseteq> set l1"
        using assms(3) read_pred_def by auto
      let ?i = "rename_state i (l1, rename_list l2 t, [], do)"
      have "?i << x"
        by (metis \<open>i << rename_state x (rename_inv (l1, rename_list l2 t, [], do))\<close> \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> semantics_algebra.wf_renaming_order semantics_algebra_axioms wf_rename_inv_other)
      moreover have "\<And>var. var \<in> \<sigma> i \<Longrightarrow> rename_elem var (l1, rename_list l2 t, [], do) = rename_elem (rename_elem var ?t) t"
      proof -
        fix var assume "var \<in> \<sigma> i"
        then obtain j where "var = l1 ! j" "j < length l1"
          by (metis \<open>\<sigma> i \<subseteq> set l1\<close> in_set_conv_nth subsetD)
        then have "rename_elem var ?t = l2 ! j"
          using assms(2) rename_elem_in_l1_l2 by blast
        moreover have "rename_elem (l2 ! j) t = (rename_list l2 t) ! j"
          using \<open>j < length l1\<close> \<open>length l1 = length l2\<close> rename_list_def by auto
        ultimately show "rename_elem var (l1, rename_list l2 t, [], do) = rename_elem (rename_elem var ?t) t"
          using \<open>j < length l1\<close> \<open>var = l1 ! j\<close> \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> rename_elem_in_l1_l2 by auto
      qed
      then have "?i = rename_state (rename_state i ?t) t"
        using \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> assms(1) assms(2) rename_state_double by auto
      then have "i << ?x2"
        by (metis assms(1) assms(2) calculation rename_inv_def_state renaming_invert_wf wf_renaming_order)
      then show ?thesis
        using \<open>i \<in> Inh P\<close> bigger_set_def by blast
    qed
    moreover have "?b \<Longrightarrow> ?a"
    proof -
      assume "?b"
      then obtain i where "i \<in> Inh P" "i << ?x2"
        using bigger_set_def by auto
      then have "\<sigma> i \<subseteq> set l1"
        using assms(3) read_pred_def by auto
      let ?i = "rename_state (rename_state i ?t) t"
      have "?i << x"
        by (metis \<open>i << rename_state (rename_state x (rename_inv t)) (rename_inv (l1, l2, [], do))\<close> assms(1) assms(2) semantics_algebra.wf_renaming_order semantics_algebra_axioms wf_rename_inv_other)
      moreover have "\<And>var. var \<in> \<sigma> i \<Longrightarrow> rename_elem var (l1, rename_list l2 t, [], do) = rename_elem (rename_elem var ?t) t"
      proof -
        fix var assume "var \<in> \<sigma> i"
        then obtain j where "var = l1 ! j" "j < length l1"
          by (metis \<open>\<sigma> i \<subseteq> set l1\<close> in_set_conv_nth subsetD)
        then have "rename_elem var ?t = l2 ! j"
          using assms(2) rename_elem_in_l1_l2 by blast
        moreover have "rename_elem (l2 ! j) t = (rename_list l2 t) ! j"
          using \<open>j < length l1\<close> \<open>length l1 = length l2\<close> rename_list_def by auto
        ultimately show "rename_elem var (l1, rename_list l2 t, [], do) = rename_elem (rename_elem var ?t) t"
          using \<open>j < length l1\<close> \<open>var = l1 ! j\<close> \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> rename_elem_in_l1_l2 by auto
      qed
      then have "?i = rename_state i (l1, rename_list l2 t, [], do)"
        by (metis \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> assms(1) assms(2) rename_state_double)
      then have "i << ?x1"
        by (metis \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> calculation rename_inv_def_state renaming_invert_wf wf_renaming_order)
      then show ?thesis
        using \<open>i \<in> Inh P\<close> bigger_set_def by blast
    qed
    ultimately show ?thesis by blast
  qed
  moreover have "?ra x = None \<longleftrightarrow> ?rb x = None"
  proof -
    have "?ra x = P ?x1"
      using calculation(1) by blast
    moreover have "?rb x = P ?x2"
      using rename_pred_def by auto
    moreover obtain V where V_def: "set V = \<sigma> x - set (rename_list l2 t)" 
      by (meson finite_Diff finite_list finite_store)
    let ?tt = "rename_inv (l1, rename_list l2 t, [], do)"
    let ?x = "h_comp (rename_state x ?tt) (rename_list V ?tt)"
    have "?x << ?x1"
      using h_comp_sum commutative_monoid.s_core_def commutative_monoid_axioms smaller_def by fastforce
    moreover have "set (rename_list V ?tt) \<inter> set l1 = {}"
    proof -
      have "set (rename_list V ?tt) \<inter> set l1 \<subseteq> {}"
      proof (rule subsetI)
        fix xx assume "xx \<in> set (rename_list V ?tt) \<inter> set l1"
        then obtain v where "v \<in> set V" "xx = rename_elem v ?tt" using rename_list_def by auto
        then have "v \<in> \<sigma> x - set (rename_list l2 t)" 
          using \<open>set V = \<sigma> x - set (rename_list l2 t)\<close> by blast
        moreover have "rename_elem xx (l1, rename_list l2 t, [], do) \<in> set (rename_list l2 t)"
        proof (rule wf_renaming_in_old)
          show "wf_renaming (l1, rename_list l2 t, [], do)" 
            using \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> by blast
          show "xx \<in> set l1" 
            using \<open>xx \<in> set (rename_list V (rename_inv (l1, rename_list l2 t, [], do))) \<inter> set l1\<close> by blast
        qed
        moreover have "rename_elem xx (l1, rename_list l2 t, [], do) = v" 
          by (metis \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> \<open>xx = rename_elem v (rename_inv (l1, rename_list l2 t, [], do))\<close> rename_inv_def_elem renaming_invert_wf)
        ultimately show "xx \<in> {}" by blast
      qed
      then show ?thesis by simp
    qed

    ultimately have "P ?x = P ?x1" 
      by (metis (no_types, lifting) assms(3) inf_sup_distrib1 read_pred_h_comp sup.orderE sup_bot.left_neutral)

    moreover have "P ?x = P ?x2"
    proof -
      have "h_comp (rename_state (rename_state x ?t1) ?t2) (rename_list (rename_list V ?t1) ?t2)
 = rename_state (rename_state (h_comp x V) ?t1) ?t2"
        using assms(1) assms(2) rename_h_comp renaming_invert_wf by auto

      moreover have "rename_state (h_comp x V) ?tt = ?x"
        
        using \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> rename_h_comp renaming_invert_wf by blast
      moreover have "rename_state (h_comp x V) ?tt = rename_state (rename_state (h_comp x V) ?t1) ?t2"
      proof (rule rename_state_double)
        show "wf_renaming (rename_inv (l1, rename_list l2 t, [], do))" 
          using \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> renaming_invert_wf by blast
        show "wf_renaming ?t1" 
          by (simp add: assms(1) renaming_invert_wf)
        show "wf_renaming ?t2" 
          using assms(2) renaming_invert_wf by blast
        have "\<And>xx. xx\<in>\<sigma> (h_comp x V) \<Longrightarrow> rename_elem xx (rename_inv (l1, rename_list l2 t, [], do)) = rename_elem (rename_elem xx ?t1) ?t2"
        proof -
          fix xx assume "xx \<in> \<sigma> (h_comp x V)"
          then have "xx \<in> set (rename_list l2 t)" 
            by (simp add: V_def h_comp_store)
          then obtain i where "i < length (rename_list l2 t)" "xx = rename_list l2 t ! i" 
            by (metis in_set_conv_nth)
          then have "rename_elem xx (rename_inv (l1, rename_list l2 t, [], do)) = l1 ! i" 
            using \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> wf_renaming_inv_in_new by blast
          moreover have "xx = rename_elem (l2 ! i) t" 
            using \<open>i < length (rename_list l2 t)\<close> \<open>xx = rename_list l2 t ! i\<close> rename_list_def by auto
          then have "rename_elem xx ?t1 = l2 ! i"
            by (simp add: assms(1) rename_inv_def_elem)
          then show "rename_elem xx (rename_inv (l1, rename_list l2 t, [], do)) = rename_elem (rename_elem xx ?t1) ?t2"
            using \<open>i < length (rename_list l2 t)\<close> \<open>wf_renaming (l1, rename_list l2 t, [], do)\<close> assms(2) calculation wf_renaming_inv_in_new by auto
        qed
        then show "\<forall>x\<in>\<sigma> (h_comp x V). rename_elem x (rename_inv (l1, rename_list l2 t, [], do)) = rename_elem (rename_elem x ?t1) ?t2"
          by blast
      qed
      then have "?x << ?x2" 
        by (metis calculation(1) calculation(2) h_comp_sum commutative_monoid.s_core_def commutative_monoid_axioms smaller_def)
      moreover have "C ?x = C ?x2" 
        by (metis \<open>rename_state (h_comp x V) (rename_inv (l1, rename_list l2 t, [], do)) = rename_state (rename_state (h_comp x V) (rename_inv t)) (rename_inv (l1, l2, [], do))\<close> calculation(1) calculation(2) h_comp_same_C)
      moreover have "(\<sigma> ?x2 - \<sigma> ?x) \<inter> set (read_pred P) = {}"
      proof -
        have "\<sigma> ?x = \<sigma> ?x2 - set (rename_list (rename_list V ?t1) ?t2)" 
          by (metis \<open>rename_state (h_comp x V) (rename_inv (l1, rename_list l2 t, [], do)) = rename_state (rename_state (h_comp x V) (rename_inv t)) (rename_inv (l1, l2, [], do))\<close> calculation(1) calculation(2) h_comp_store)
        moreover have "set (rename_list (rename_list V ?t1) ?t2) \<inter> set l1 \<subseteq> {}"
        proof (rule subsetI)
          fix xx assume "xx \<in> set (rename_list (rename_list V ?t1) ?t2) \<inter> set l1"
          then obtain v where "v \<in> set V" "xx = rename_elem (rename_elem v ?t1) ?t2" using rename_list_def by auto
          then have "v \<in> \<sigma> x - set (rename_list l2 t)" 
            using \<open>set V = \<sigma> x - set (rename_list l2 t)\<close> by blast
          moreover have "rename_elem xx (l1, l2, [], do) \<in> set l2"
            using \<open>xx \<in> set (rename_list (rename_list V (rename_inv t)) (rename_inv (l1, l2, [], do))) \<inter> set l1\<close> assms(2) wf_renaming_in_old by auto
          then have "rename_elem (rename_elem xx (l1, l2, [], do)) t \<in> set (rename_list l2 t)"
            using rename_list_def by auto
          moreover have "rename_elem (rename_elem xx (l1, l2, [], do)) t = v" 
            by (metis \<open>xx = rename_elem (rename_elem v (rename_inv t)) (rename_inv (l1, l2, [], do))\<close> assms(1) assms(2) rename_inv_def_elem renaming_invert_wf)
          ultimately show "xx \<in> {}" by blast
        qed
          ultimately show ?thesis 
          using assms(3) by fastforce
      qed
      ultimately show "P ?x = P ?x2"
        by (metis pred_read_pred_same)
    qed
    then show ?thesis
      using calculation rename_pred_def by auto
  qed
  ultimately show "?ra x = ?rb x"
    using \<open>rename_pred (rename_pred P (l1, l2, [], do)) t x = rename_pred P (l1, l2, [], do) (rename_state x (rename_inv t))\<close> assms(4) wf_assert_def
    by (smt not_Some_eq)
qed

lemma renaming_inv_in_list:
  assumes "wf_renaming (l1, l2, l3, do)"
      and "i < length l2"
      and "y = l2 ! i"
    shows "rename_elem y (rename_inv (l1, l2, l3, do)) = l1 ! i"
  by (metis assms(1) assms(2) assms(3) rename_elem_in_l1_l2 rename_inv_def_elem wf_renaming.simps)

lemma rename_doesnt_change_if_not_affected:
  assumes "wf_renaming (l1, l2, [], do)"
      and "set (read_pred P) \<subseteq> set l1"
      and "wf_assert P"
    shows "rename_pred P (l1, l2, [], do) = rename_pred P (l1, l2, l, d)"
proof (rule ext)
  fix x
  let ?t = "(l1, l2, [], do)"
  let ?t' = "(l1, l2, l, d)"
  show "rename_pred P ?t x = rename_pred P ?t' x" (is "?a x = ?b x")
  proof -
    let ?x = "rename_state x (rename_inv ?t)"
    let ?x' = "rename_state x (rename_inv ?t')"

    have "P ?x = P ?x'"
    proof -
      obtain V where "set V = \<sigma> x - set l2"
        by (meson finite_Diff finite_list finite_store)
      let ?xx = "h_comp x V"
      have "\<sigma> ?xx \<subseteq> set l2" 
        by (simp add: Diff_Diff_Int \<open>set V = \<sigma> x - set l2\<close> h_comp_store)
      then have "\<And>xx. xx \<in> \<sigma> ?xx \<Longrightarrow> rename_elem xx (rename_inv ?t) = rename_elem xx (rename_inv ?t')"
      proof -
        fix xx assume "xx \<in> \<sigma> ?xx"
        then have "xx \<in> set l2" 
          by (simp add: \<open>set V = \<sigma> x - set l2\<close> h_comp_store)
        then obtain i where "i < length l2" "xx = l2 ! i" 
          by (metis in_set_conv_nth)
        then have "rename_elem xx (rename_inv ?t) = l1 ! i" using renaming_inv_in_list
          using assms(1) by blast
        moreover have "rename_elem xx (rename_inv ?t') = l1 ! i" 
          using \<open>i < length l2\<close> \<open>xx = l2 ! i\<close> assms(1) renaming_inv_in_list by auto
        ultimately show "rename_elem xx (rename_inv ?t) = rename_elem xx (rename_inv ?t')" by simp
      qed
      then have "rename_state ?xx (rename_inv ?t) = rename_state ?xx (rename_inv ?t')"
        using assms(1) rename_state_same renaming_invert_wf by auto
      moreover have "rename_state ?xx (rename_inv ?t) << ?x"
        by (metis assms(1) h_comp_sum commutative_monoid.s_core_def commutative_monoid_axioms rename_h_comp semantics_algebra.renaming_invert_wf semantics_algebra_axioms smaller_def)

      moreover have "P ?x = P (h_comp (rename_state x (rename_inv ?t)) (rename_list V (rename_inv ?t)))"
      proof (rule read_pred_h_comp)
        have "set (rename_list V (rename_inv (l1, l2, [], do))) \<inter> set (read_pred P) \<subseteq> {}"
        proof (rule subsetI)
          let ?l = "rename_list V (rename_inv (l1, l2, [], do))"
          fix y assume asm5: "y \<in> set ?l \<inter> set (read_pred P)"
          then obtain yy where "yy \<in> set V" "y = rename_elem yy (rename_inv (l1, l2, [], do))" 
            by (smt IntD1 image_iff semantics_algebra.rename_list_def semantics_algebra_axioms set_map)
          then have "yy \<notin> set l2" 
            by (simp add: \<open>set V = \<sigma> x - set l2\<close>)
          moreover have "rename_elem y (l1, l2, [], do) = yy"
            by (metis \<open>y = rename_elem yy (rename_inv (l1, l2, [], do))\<close> assms(1) rename_inv_def_elem renaming_invert_wf)
          then have "y \<notin> set l1" 
            by (metis assms(1) calculation in_set_conv_nth rename_elem_in_l1_l2 wf_renaming.simps)
          then show "y \<in> {}" 
            using asm5 assms(2) by auto
        qed
        then show "set (rename_list V (rename_inv (l1, l2, [], do))) \<inter> set (read_pred P) = {}" by simp
      qed
      moreover have "P ?x' = P (h_comp (rename_state x (rename_inv ?t')) (rename_list V (rename_inv ?t')))"
      proof (rule read_pred_h_comp)
        have "set (rename_list V (rename_inv (l1, l2, l, d))) \<inter> set (read_pred P) \<subseteq> {}"
        proof (rule subsetI)
          let ?l = "rename_list V (rename_inv (l1, l2, l, d))"
          fix y assume asm5: "y \<in> set ?l \<inter> set (read_pred P)"
          then obtain yy where "yy \<in> set V" "y = rename_elem yy (rename_inv (l1, l2, l, d))" 
            by (smt IntD1 image_iff semantics_algebra.rename_list_def semantics_algebra_axioms set_map)
          then have "yy \<notin> set l2" 
            by (simp add: \<open>set V = \<sigma> x - set l2\<close>)
          moreover have "rename_elem y (l1, l2, l, d) = yy" 
            by (metis \<open>y = rename_elem yy (rename_inv (l1, l2, l, d))\<close> assms(1) rename_inv_def_elem renaming_invert_wf wf_renaming.simps)
          then have "y \<notin> set l1" 
            by (metis assms(1) calculation in_set_conv_nth rename_elem_in_l1_l2 wf_renaming.simps)
          then show "y \<in> {}" 
            using asm5 assms(2) by auto
        qed
        then show "set (rename_list V (rename_inv (l1, l2, l, d))) \<inter> set (read_pred P) = {}" by simp
      qed
      ultimately show ?thesis 
        using \<open>rename_state (h_comp x V) (rename_inv (l1, l2, [], do)) = rename_state (h_comp x V) (rename_inv (l1, l2, l, d))\<close> assms(1) rename_h_comp renaming_invert_wf by auto
    qed
    then show ?thesis 
      by (simp add: rename_pred_def)
  qed
qed

lemma rename_removes_vars_list:
  assumes "wf_renaming (l1, l2, l3, do)"
      and "set l \<subseteq> set do"
  shows "set (rename_list l (l1, l2, l3, do)) \<inter> (set l1 \<union> set l3) \<subseteq> set l2" (is "?a \<subseteq> ?b")
proof (rule subsetI)
  fix x assume "x \<in> ?a"
  obtain i where "x = rename_list l (l1, l2, l3, do) ! i" "i < length l"
    by (metis IntD1 \<open>x \<in> set (rename_list l (l1, l2, l3, do)) \<inter> (set l1 \<union> set l3)\<close> in_set_conv_nth length_map rename_list_def)
  then show "x \<in> ?b"
    by (smt IntD2 \<open>x \<in> set (rename_list l (l1, l2, l3, do)) \<inter> (set l1 \<union> set l3)\<close> assms(1) assms(2) nth_map nth_mem rename_list_def rename_removes_vars_elem semantics_algebra_axioms subsetD)
qed

lemma list_inclusion:
  assumes "wf_renaming t"
      and "set a \<subseteq> set b"
    shows "set (rename_list a t) \<subseteq> set (rename_list b t)" (is "?a \<subseteq> ?b")
proof (rule subsetI)
  fix x assume "x \<in> ?a"
  then obtain i where "x = rename_elem (a ! i) t" "i < length a"
    by (smt in_set_conv_nth length_map nth_map rename_list_def)
  then obtain j where "a ! i = b ! j" "j < length b"
    by (metis assms(2) in_set_conv_nth subsetD)
  then have "x = rename_elem (b ! j) t"
    by (simp add: \<open>x = rename_elem (a ! i) t\<close>)
  then show "x \<in> ?b"
    using \<open>j < length b\<close> rename_list_def by auto
qed

lemma rename_list_same:
  assumes "wf_renaming (l1, l2, l3, do)"
  shows "rename_list l1 (l1, l2, l3, do) = l2"
proof -
  have "length (rename_list l1 (l1, l2, l3, do)) = length l2"
    using assms rename_list_def by auto
  moreover have "\<And>i. i < length l2 \<Longrightarrow> rename_list l1 (l1, l2, l3, do) ! i = l2 ! i"
    using assms rename_elem_in_l1_l2 rename_list_def by auto
  ultimately show ?thesis
    by (simp add: list_eq_iff_nth_eq)
qed

lemma rename_modif_for_q: 
  assumes "wf_renaming (l1, l2, l3, do)"
      and "set (read_pred Q) \<subseteq> set l1"
    shows "set (read_pred (rename_pred Q (l1, l2, l3, do))) \<subseteq> set l2" (is "?a \<subseteq> ?b")
proof -
  let ?t = "(l1, l2, l3, do)"
  have "set (read_pred (rename_pred Q ?t)) = set (rename_list (read_pred Q) ?t)"
    using assms(1) read_pred_rename_pred rename_list_def by auto
  moreover have "set (rename_list (read_pred Q) ?t) \<subseteq> set (rename_list l1 ?t)"
    using assms(1) assms(2) list_inclusion by blast
  moreover have "rename_list l1 ?t = l2"
    using assms(1) rename_list_same by blast
  ultimately show ?thesis by simp
qed

lemma rename_removes_vars_pred:
  assumes "wf_renaming (l1, l2, l3, do)"
      and "set (read_pred P) \<subseteq> set do"
  shows "set (read_pred (rename_pred P (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3) \<subseteq> set l2"
proof -
  have "set (read_pred (rename_pred P (l1, l2, l3, do))) = set (rename_list (read_pred P) (l1, l2, l3, do))"
    using assms read_pred_rename_pred rename_list_def by auto
  then show ?thesis
    using assms rename_removes_vars_list by auto
qed

lemma rename_inv_def_pred:
  assumes "wf_renaming t"
  shows "rename_pred (rename_pred P t) (rename_inv t) = P"
proof (rule ext)
  fix x
  show "rename_pred (rename_pred P t) (rename_inv t) x = P x"
    by (metis assms rename_inv_def_state rename_pred_def renaming_invert_wf)
qed

lemma rename_pred_lnot:
  "rename_pred (lnot b) t = lnot (rename_pred b t)"
  apply (rule ext)
  by (simp add: lnot_def rename_pred_def)

lemma rename_list_same_length: "wf_renaming t \<Longrightarrow> length (rename_list l t) = length l"
  by (simp add: rename_list_def)

lemma rename_list_concat: "wf_renaming t \<Longrightarrow> rename_list (l1 @ l2) t = rename_list l1 t @ rename_list l2 t"
  apply (induct l1)
  apply (metis append_Nil length_0_conv rename_list_same_length)
  by (simp add: rename_list_def)

lemma rename_elem_list:
  assumes "i < length l"
      and "wf_renaming t"
    shows "rename_list l t ! i = rename_elem (l ! i) t"
  by (simp add: assms(1) rename_list_def)

lemma rename_list_distinct:
  assumes "wf_renaming t"
  and "distinct l"
  shows "distinct (rename_list l t)"
proof (rule ccontr)
  let ?t = "rename_inv t"
  assume "\<not> distinct (rename_list l t)"
  then obtain i j where "i \<noteq> j" "rename_list l t ! i = rename_list l t ! j" "i < length l" "j < length l"
    using distinct_conv_nth
    by (metis assms(1) rename_list_same_length)
  then have "rename_elem (l ! i) t = rename_elem (l ! j) t"
    by (smt \<open>\<not> distinct (rename_list l t)\<close> assms(1) assms(2) distinct_conv_nth rename_elem_list rename_inv_def_elem rename_list_same_length)
  then have "rename_elem (rename_elem (l ! i) t) ?t = rename_elem (rename_elem (l ! j) t) ?t"
    by simp
  then have "l ! i = l ! j"
    using assms(1) rename_inv_def_elem by auto
  then have "\<not> distinct l"
    using \<open>i < length l\<close> \<open>i \<noteq> j\<close> \<open>j < length l\<close> nth_eq_iff_index_eq by blast
  then show "False" using assms(2)
    by blast
qed

fun modif :: "('a, 'b, 'c) stmt \<Rightarrow> 'b list" where
  "modif (s1 ; s2) = modif s1 @ modif s2"
| "modif (If s1 s2) = modif s1 @ modif s2"
| "modif (MethodCall y m x) = y"
| "modif (While b I s) = modif s"
| "modif (Assume b) = []"
| "modif (Inhale P) = []"
| "modif (Exhale P) = []"
| "modif (Var l) = l"
| "modif (Havoc l) = l"
| "modif Skip = []"
| "modif (Other s) = modif_other s"

definition filter_sigma :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "filter_sigma \<phi> V = filter (\<lambda>x. x \<in> \<sigma> \<phi>) V"

subsection \<open>Semantics\<close>

function semantics :: "('a, 'b, 'c) program \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> 'a ss" where
  "semantics Pr \<phi> Skip = S {\<phi>}"
| "semantics Pr \<phi> (Assume b) = (if well_defined_assert b \<phi> then if b \<phi> = Some True then S {\<phi>} else S {}
  else Error)"

| "semantics Pr \<phi> (s1 ; s2) = (let r = semantics Pr \<phi> s1 in
  if r = Error then Error
  else let A = get_S r in
    union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s2) ` A))"

| "semantics Pr \<phi> (If s1 s2) = (let r1 = semantics Pr \<phi> s1 in
    let r2 = semantics Pr \<phi> s2 in
    if r1 = Error \<or> r2 = Error then Error
    else S (get_S r1 \<union> get_S r2))"

| "semantics Pr \<phi> (Var x) = (if set x \<inter> \<sigma> \<phi> = {} then S ({\<phi>} \<oplus>\<oplus> h x) else Error)"
| "semantics Pr \<phi> (Other s) = semantics_other Pr \<phi> s"
| "semantics Pr \<phi> (Havoc x) = (if set x \<subseteq> \<sigma> \<phi> then S ({h_comp \<phi> x} \<oplus>\<oplus> h x) else Error)"

| "semantics Pr \<phi> (Inhale P) = (if well_defined_assert P \<phi> then S ({\<phi>} \<oplus>\<oplus> Inh P) else Error)"
| "semantics Pr \<phi> (Exhale P) =
  (if P \<phi> = Some True \<and> well_defined_assert P \<phi> then S {\<phi>' | \<phi>' i r. Some \<phi> = Some i \<oplus> Some r \<and> i \<in> Inh P \<and> Some \<phi>' = s_core i \<oplus> Some r}
  else Error)"

| "semantics Pr \<phi> (MethodCall y m x) = (
  if set x \<union> set y \<subseteq> \<sigma> \<phi> then
    let (_, args, ret, P, Q, _) = the (get_method Pr m) in semantics Pr \<phi>
    (Exhale (rename_pred P (args @ ret, x @ y, [], [])); Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], [])))
  else Error)"
| "semantics Pr \<phi> (While b I s) =
   (let V = filter_sigma \<phi> (modif s) in
   if semantics Pr ( |\<phi>| ) (Havoc V; Inhale I; Assume b; s ; Exhale I) = Error then
     Error
   else
     semantics Pr \<phi> (Exhale I; Havoc V; Inhale I ; Assume (lnot b)))"
by pat_completeness auto
termination
  apply(relation "measure (\<lambda>(Pr, \<phi>, s). len s)")
  using len_at_least_one less_le_trans by auto

fun read :: "('a, 'b, 'c) stmt \<Rightarrow> 'b list" where
  "read (s1 ; s2) = read s1 @ read s2"
| "read (If s1 s2) = read s1 @ read s2"
| "read (MethodCall y m x) = x @ y"
| "read (While b I s) = read s @ read_pred I @ read_pred b"
| "read (Assume b) = read_pred b"
| "read (Inhale P) = read_pred P"
| "read (Exhale P) = read_pred P"
| "read (Var l) = l"
| "read (Havoc l) = l"
| "read Skip = []"
| "read (Other s) = read_other s"

fun rename :: "('a, 'b, 'c) stmt \<Rightarrow> 'b rename_t \<Rightarrow> ('a, 'b, 'c) stmt" where
  "rename (Inhale P) t = Inhale (rename_pred P t)"
| "rename (Exhale P) t = Exhale (rename_pred P t)"
| "rename (s1 ; s2) t = (rename s1 t ; rename s2 t)"
| "rename (Var x) t = Var (rename_list x t)"
| "rename (Havoc x) t = Havoc (rename_list x t)"
| "rename (If s1 s2) t = If (rename s1 t) (rename s2 t)"
| "rename (While b I s) t = While (rename_pred b t) (rename_pred I t) (rename s t)"
| "rename (MethodCall y m x) t = MethodCall (rename_list y t) m (rename_list x t)"
| "rename (Assume b) t = Assume (rename_pred b t)"
| "rename (Other other) t = Other (rename_other other t)"
| "rename Skip t = Skip"

fun bigger_ss :: "'a ss \<Rightarrow> 'a ss \<Rightarrow> bool" (infixl ">>>" 60) where
  "_ >>> Error \<longleftrightarrow> True"
| "Error >>> _ \<longleftrightarrow> False"
| "S A >>> S B \<longleftrightarrow> A >> B"

fun sem :: "('a, 'b, 'c) program \<Rightarrow> 'a set \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> 'a set" where
  "sem Pr A s = (\<Union>a\<in>A. get_S (semantics Pr a s))"

definition ver :: "('a, 'b, 'c) program \<Rightarrow> 'a set \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "ver Pr A st \<longleftrightarrow> (\<forall>a\<in>A. semantics Pr a st \<noteq> Error)"

definition mono :: "('a, 'b, 'c) program \<Rightarrow> 'a set \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "mono Pr A s \<longleftrightarrow> (\<forall>a \<in> A. (\<forall>x y. y << a \<and> x << y \<longrightarrow> semantics Pr y s >>> semantics Pr x s))"

lemma mono_equiv_def:
  "mono Pr A s \<longleftrightarrow> (\<forall>x y. (\<exists>a \<in> A. y << a) \<and> x << y \<longrightarrow> semantics Pr y s >>> semantics Pr x s)"
  using local.mono_def by blast

definition ssafeMono :: "('a, 'b, 'c) program \<Rightarrow> 'a set \<Rightarrow> ('a, 'b, 'c) stmt  \<Rightarrow> bool" where
  "ssafeMono Pr A s \<longleftrightarrow> (\<forall>B A'. A' >> B \<and> (\<forall>a' \<in> A'. \<exists>a \<in> A. a' << a) \<and> ver Pr B s \<longrightarrow> ver Pr A' s)"

definition smonoOut :: "('a, 'b, 'c) program \<Rightarrow> 'a set \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "smonoOut Pr A s \<longleftrightarrow> (\<forall>B A'. ver Pr B s \<and> A' >> B \<and> (\<forall>a' \<in> A'. \<exists>a \<in> A. a' << a) \<longrightarrow> (sem Pr A' s >> sem Pr B s))"

definition smono :: "('a, 'b, 'c) program \<Rightarrow> 'a set \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "smono Pr A st \<longleftrightarrow> ssafeMono Pr A st \<and> smonoOut Pr A st"

lemma v_singleton: "ver Pr A s \<longleftrightarrow> (\<forall>a\<in>A. ver Pr {a} s)"
  by (simp add: ver_def)

lemma s_singleton: "sem Pr A s = (\<Union>a\<in>A. sem Pr {a} s)"
  by auto

lemma elem_sem:
  "x \<in> sem Pr A s \<longleftrightarrow> (\<exists>a\<in>A. x \<in> sem Pr {a} s)"
  using UN_E s_singleton by simp

lemma smaller_error:
  assumes "Error >>> x"
  shows "x = Error"
  using assms bigger_ss.elims(2) by blast

lemma bigger_not_error:
  assumes "x >>> y"
      and "y \<noteq> Error"
    shows "x \<noteq> Error"
  using assms(1) assms(2) smaller_error by blast

lemma ssafeMono_singleton:
  "ssafeMono Pr A s \<longleftrightarrow> (\<forall>x y. x << y \<and> (\<exists>a \<in> A. y << a) \<longrightarrow> (ver Pr {x} s \<longrightarrow> ver Pr {y} s))" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b"
  proof -
    assume "?a"
    have "\<And>a b. b << a \<and> (\<exists>x \<in> A. a << x) \<Longrightarrow> (ver Pr {b} s \<longrightarrow> ver Pr {a} s)"
    proof -
      fix a b assume "b << a \<and> (\<exists>x \<in> A. a << x)"
      then have "{a} >> {b}" using bigger_set_def by blast
      then show "ver Pr {b} s \<longrightarrow> ver Pr {a} s"
        using \<open>b << a \<and> (\<exists>x\<in>A. a << x)\<close> \<open>ssafeMono Pr A s\<close> ssafeMono_def by auto
    qed
    then show "?b" by blast
  qed
  moreover have "?b \<Longrightarrow> ?a"
  proof -
    assume "?b"
    then have "\<And>A' B. A' >> B \<and> (\<forall>a' \<in> A'. \<exists>a \<in> A. a' << a) \<Longrightarrow> (ver Pr B s \<longrightarrow> ver Pr A' s)"
    proof -
      fix A' B assume "A' >> B \<and>  (\<forall>a' \<in> A'. \<exists>a \<in> A. a' << a)"
      then have "ver Pr B s \<Longrightarrow> ver Pr A' s"
      proof -
        assume "ver Pr B s"
        then have "\<forall>b\<in>B. ver Pr {b} s" by (meson v_singleton)
        moreover have "\<forall>a\<in>A'. \<exists>b\<in>B. b << a"
          using \<open>A' >> B \<and> (\<forall>a'\<in>A'. \<exists>a\<in>A. a' << a)\<close> bigger_set_def by blast
        then have "\<forall>a\<in>A'. ver Pr {a} s"
          using \<open>A' >> B \<and> (\<forall>a'\<in>A'. \<exists>a\<in>A. a' << a)\<close> \<open>\<forall>x y. x << y \<and> (\<exists>a\<in>A. y << a) \<longrightarrow> ver Pr {x} s \<longrightarrow> ver Pr {y} s\<close> calculation by blast
        then show "ver Pr A' s"
          using v_singleton by blast
      qed
      then show "ver Pr B s \<longrightarrow> ver Pr A' s" by auto
    qed
    then show "?a"
      using ssafeMono_def by auto
  qed
  ultimately show ?thesis by blast
qed

lemma ssafeMonoI:
  "(\<And>x y. x << y \<and> (\<exists>a \<in> A. y << a) \<and> ver Pr {x} s \<Longrightarrow> ver Pr {y} s) \<Longrightarrow> ssafeMono Pr A s"
  using ssafeMono_singleton by blast

lemma smonoOut_singleton:
  "smonoOut Pr A s \<longleftrightarrow> (\<forall>a b. ver Pr {b} s \<and> b << a \<and> (\<exists>x \<in> A. a << x) \<longrightarrow> (sem Pr {a} s >> sem Pr {b} s))" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b"
    by (metis (no_types, lifting) bigger_set_def empty_subsetI insert_mono mk_disjoint_insert singletonD singletonI smonoOut_def)    
  moreover have "?b \<Longrightarrow> ?a"
  proof -
    assume "?b"
    then have "\<And>A' B. ver Pr B s \<and> A' >> B \<and> (\<forall>a' \<in> A'. \<exists>a \<in> A. a' << a) \<Longrightarrow> (sem Pr A' s >> sem Pr B s)"
    proof -
      fix A' B assume "ver Pr B s \<and> A' >> B \<and> (\<forall>a' \<in> A'. \<exists>a \<in> A. a' << a)"
      then have "\<And>sa. sa \<in> (sem Pr A' s) \<Longrightarrow> (\<exists>sb \<in> sem Pr B s. sb << sa)"
      proof -
        fix sa assume "sa \<in> sem Pr A' s"
        then obtain a where "a \<in> A'" "sa \<in> sem Pr {a} s" using elem_sem by blast
        then obtain b where "b \<in> B" "b << a"
          using \<open>ver Pr B s \<and> A' >> B \<and> (\<forall>a' \<in> A'. \<exists>a \<in> A. a' << a)\<close> bigger_set_def by auto
        then have "sem Pr {a} s >> sem Pr {b} s"
          by (meson \<open>\<forall>a b. ver Pr {b} s \<and> b << a \<and> (\<exists>x \<in> A. a << x) \<longrightarrow> sem Pr {a} s >> sem Pr {b} s\<close> \<open>a \<in> A'\<close> \<open>ver Pr B s \<and> A' >> B \<and> (\<forall>a' \<in> A'. \<exists>a \<in> A. a' << a)\<close> in_mono v_singleton)
        then obtain sb where "sb \<in> sem Pr {b} s" "sb << sa" using \<open>sa \<in> sem Pr {a} s\<close> bigger_set_def by auto
        then show "\<exists>sb \<in> sem Pr B s. sb << sa" using \<open>b \<in> B\<close> elem_sem by blast
      qed
      then show "sem Pr A' s >> sem Pr B s" using bigger_set_def by simp
    qed
    then show "?a" by (simp add: smonoOut_def)
  qed
  ultimately show ?thesis by blast
qed

lemma smonoOutI:
  "(\<And>a b. ver Pr {b} s \<and> b << a \<and> (\<exists>x \<in> A. a << x) \<Longrightarrow> (sem Pr {a} s >> sem Pr {b} s)) \<Longrightarrow> smonoOut Pr A s"
  using smonoOut_singleton by blast

lemma triple_not_error:
  assumes "A >>> B"
      and "B \<noteq> Error"
    shows "get_S A >> get_S B"
  by (metis assms(1) assms(2) bigger_ss.elims(2) get_S.simps(1))

lemma singleton_semantics:
  assumes "semantics Pr a s = S A"
  shows "sem Pr {a} s = A"
proof -
  have "sem Pr {a} s = (\<Union>a\<in>{a}. get_S (semantics Pr a s))"
    by simp
  then show ?thesis
    by (simp add: assms)
qed

lemma triple_not_error_semantics:
  assumes "semantics Pr a s >>> semantics Pr b s"
      and "semantics Pr b s \<noteq> Error"
    shows "sem Pr {a} s >> sem Pr {b} s"
proof -
  obtain A B where "semantics Pr a s = S A" "semantics Pr b s = S B"
    using assms(1) assms(2) bigger_ss.elims(2) by blast
  then have "A >> B"
    using assms(1) by auto
  then show ?thesis
    by (simp add: \<open>semantics Pr a s = S A\<close> \<open>semantics Pr b s = S B\<close>)
qed

(* TODO *)

lemma mono_smono:
  "mono Pr A s \<longleftrightarrow> smono Pr A s" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b"
  proof -
    assume "?a"
    then have "\<And>a b. b << a \<and> (\<exists>x \<in> A. a << x) \<and> ver Pr {b} s \<Longrightarrow> ver Pr {a} s"
    proof -
      fix a b assume "b << a \<and> (\<exists>x \<in> A. a << x) \<and> ver Pr {b} s"
      then show "ver Pr {a} s"
        using \<open>local.mono Pr A s\<close> local.mono_def smaller_error ver_def by fastforce
    qed
    then have "ssafeMono Pr A s"
      using ssafeMono_singleton by blast
    moreover have "smonoOut Pr A s"
    proof -
      have "\<And>a b. ver Pr {b} s \<and> b << a \<and> (\<exists>x \<in> A. a << x) \<Longrightarrow> sem Pr {a} s >> sem Pr {b} s"
      proof -
        fix a b assume "ver Pr {b} s \<and> b << a \<and> (\<exists>x \<in> A. a << x)"
        then have "semantics Pr b s \<noteq> Error" by (simp add: ver_def)
        moreover obtain aa where "aa \<in> A" "a << aa" "b << aa"
          using \<open>ver Pr {b} s \<and> b << a \<and> (\<exists>x\<in>A. a << x)\<close> smaller_trans by blast
        ultimately have "semantics Pr a s >>> semantics Pr b s"
          using \<open>local.mono Pr A s\<close> \<open>ver Pr {b} s \<and> b << a \<and> (\<exists>x \<in> A. a << x)\<close> local.mono_def by blast
        moreover have "semantics Pr a s \<noteq> Error"
          using \<open>semantics Pr b s \<noteq> Error\<close> bigger_not_error calculation by blast
        ultimately show "sem Pr {a} s >> sem Pr {b} s"
          using \<open>semantics Pr b s \<noteq> Error\<close> triple_not_error_semantics by blast
      qed
      then show ?thesis by (simp add: smonoOut_singleton)
    qed
    ultimately show ?thesis using smono_def by blast
  qed
  moreover have "?b \<Longrightarrow> ?a"
  proof -
    assume "?b"
    then have "\<And>a b. (\<exists>x \<in> A. a << x) \<and> b << a \<Longrightarrow> semantics Pr a s >>> semantics Pr b s"
    proof -
      fix a b assume "(\<exists>x \<in> A. a << x) \<and> b << a"
      then show "semantics Pr a s >>> semantics Pr b s"
      proof (cases "semantics Pr b s = Error")
        case True
        then show ?thesis by simp
      next
        case False
        then have ver_b: "ver Pr {b} s" using ver_def by auto
        then have "ver Pr {a} s"
          by (meson \<open>(\<exists>x \<in> A. a << x) \<and> b << a\<close> \<open>smono Pr A s\<close> semantics_algebra.ssafeMono_singleton semantics_algebra_axioms smono_def)
        then obtain sa sb where "semantics Pr a s = S sa" "semantics Pr b s = S sb"
          by (meson False get_S.elims ver_def semantics_algebra_axioms singleton_iff)
        moreover have "sem Pr {a} s >> sem Pr {b} s"
          by (meson \<open>(\<exists>x \<in> A. a << x) \<and> b << a\<close> \<open>smono Pr A s\<close> semantics_algebra.smonoOut_singleton semantics_algebra_axioms smono_def ver_b)
        moreover obtain "sem Pr {a} s = sa" "sem Pr {b} s = sb" by (simp add: calculation)
        ultimately show ?thesis by simp
      qed
    qed
    then show ?thesis
      using local.mono_def by auto
  qed
  ultimately show ?thesis by blast
qed

fun wf_stmt :: "('a, 'b, 'c) program \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "wf_stmt Pr (s1; s2) \<longleftrightarrow> wf_stmt Pr s1 \<and> wf_stmt Pr s2"
| "wf_stmt Pr (If s1 s2) \<longleftrightarrow> wf_stmt Pr s1 \<and> wf_stmt Pr s2"
| "wf_stmt Pr (While b I s) \<longleftrightarrow> wf_assert I \<and> wf_stmt Pr s"
| "wf_stmt Pr (MethodCall y m x) \<longleftrightarrow> (let r = get_method Pr m in
  r \<noteq> None \<and> (let (_, args, ret, _, _, _) = the r in length x = length args
  \<and> length y = length ret \<and> distinct (x @ y)))"
| "wf_stmt Pr (Inhale P) \<longleftrightarrow> wf_assert P"
| "wf_stmt Pr (Exhale P) \<longleftrightarrow> wf_assert P"
| "wf_stmt Pr (Other other) \<longleftrightarrow> wf_other Pr other"
| "wf_stmt Pr _ \<longleftrightarrow> True"

fun wf_method :: "('a, 'b, 'c) program \<Rightarrow> ('a, 'b, 'c) method \<Rightarrow> bool" where
  "wf_method Pr (m, args, ret, P, Q, s) \<longleftrightarrow>
    wf_assert P \<and> wf_assert Q \<and> distinct (args @ ret) \<and> set args \<inter> set (modif s) = {} \<and>
    set (read_pred P) \<subseteq> set args \<and> wf_stmt Pr s \<and> set (read_pred Q) \<subseteq> set args \<union> set ret"

fun wf_program_aux :: "('a, 'b, 'c) program \<Rightarrow> ('a, 'b, 'c) program \<Rightarrow> bool" where
  "wf_program_aux Pr [] \<longleftrightarrow> True"
| "wf_program_aux Pr (t # q) \<longleftrightarrow> wf_method Pr t \<and> wf_program_aux Pr q"

fun wf_program :: "('a, 'b, 'c) program \<Rightarrow> bool" where
  "wf_program Pr \<longleftrightarrow> wf_program_aux Pr Pr"

lemma get_method_same_name:
  "get_method Pr m \<noteq> None \<Longrightarrow> fst (the (get_method Pr m)) = m"
  by (induction Pr) auto

lemma simple_method_exists:
  assumes "wf_stmt Pr (MethodCall y m x)"
    shows "\<exists>args ret P Q s. get_method Pr m = Some (m, args, ret, P, Q, s)"
proof -
  obtain r where "r = get_method Pr m" by simp
  then obtain name args ret P Q s where "get_method Pr m = Some (name, args, ret, P, Q, s)"
    using assms by fastforce
  then have "m = name"
    using get_method_same_name by fastforce
  then show ?thesis
    using \<open>get_method Pr m = Some (name, args, ret, P, Q, s)\<close> by blast
qed

lemma sem_loop:
  assumes "ver Pr {\<phi>} (While b I s)"
  shows "sem Pr {\<phi>} (While b I s) = sem Pr {\<phi>} (Exhale I; Havoc (filter_sigma \<phi> (modif s)); Inhale I; Assume (lnot b))" (is "?a = ?b")
proof -
  have "semantics Pr \<phi> (While b I s) = semantics Pr \<phi> (Exhale I; Havoc (filter_sigma \<phi> (modif s)); Inhale I ; Assume (lnot b))"
    by (smt assms filter_cong semantics.simps(11) singletonI ver_def)
  then show ?thesis
    by auto
qed

lemma ver_method_real:
  assumes "get_method Pr m = Some (m, args, ret, P, Q, s)"
  shows "ver Pr {\<phi>} (MethodCall y m x) \<longleftrightarrow>
          ver Pr {\<phi>} (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], []))) \<and>
          (set x \<union> set y) \<subseteq> \<sigma> \<phi>"
  using ver_def assms by simp

lemma ver_loop: "ver Pr {\<phi>} (While b I s) \<longleftrightarrow> 
  ver Pr {\<phi>} (Exhale I; Havoc (filter_sigma \<phi> (modif s)); Inhale I ; Assume (lnot b)) \<and>
  ver Pr { |\<phi>| } (Havoc (filter_sigma \<phi> (modif s)); Inhale I; Assume b; s ; Exhale I)"
proof -
  have "semantics Pr \<phi> (While b I s) =
   (if semantics Pr ( |\<phi>| ) (Havoc (filter_sigma \<phi> (modif s)); Inhale I; Assume b; s ; Exhale I) = Error then
     Error
   else
     semantics Pr \<phi> (Exhale I; Havoc (filter_sigma \<phi> (modif s)); Inhale I ; Assume (lnot b)))"
    by auto
  then show ?thesis
    by (metis (no_types, lifting) singletonD singletonI ver_def)
qed

lemma sem_method_real:
  assumes "get_method Pr m = Some (m, args, ret, P, Q, s)"
      and "ver Pr {\<phi>} (MethodCall y m x)"
  shows "sem Pr {\<phi>} (MethodCall y m x) =
         sem Pr {\<phi>} (Exhale (rename_pred P (args @ ret, x @ y, [], [])); Havoc y ;
                      Inhale (rename_pred Q (args @ ret, x @ y, [], [])))"
proof -
  have "semantics Pr \<phi> (MethodCall y m x) = (
  if set x \<union> set y \<subseteq> \<sigma> \<phi> then
    let (_, args, ret, P, Q, _) = the (get_method Pr m) in semantics Pr \<phi>
    (Exhale (rename_pred P (args @ ret, x @ y, [], [])); Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], [])))
  else Error)" by simp
  moreover have "set x \<union> set y \<subseteq> \<sigma> \<phi>" using ver_method_real assms by simp
  ultimately have "semantics Pr \<phi> (MethodCall y m x) = (
    let (_, args, ret, P, Q, _) = the (get_method Pr m) in semantics Pr \<phi>
    (Exhale (rename_pred P (args @ ret, x @ y, [], [])); Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], []))))" by simp
  then have "semantics Pr \<phi> (MethodCall y m x) = (
    semantics Pr \<phi>
    (Exhale (rename_pred P (args @ ret, x @ y, [], [])); Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], []))))"
    using assms by simp
  moreover have "ver Pr {\<phi>}
    (Exhale (rename_pred P (args @ ret, x @ y, [], [])); Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], [])))"
    using assms(1) assms(2) ver_method_real by blast
  ultimately show ?thesis
    by simp
qed

definition well_defined_assert_set :: "'a assertion \<Rightarrow> 'a set \<Rightarrow> bool" where
  "well_defined_assert_set P A \<longleftrightarrow> (\<forall>a\<in>A. well_defined_assert P a)"

lemma ver_inhale_single:
  "well_defined_assert P \<phi> \<longleftrightarrow> ver Pr {\<phi>} (Inhale P)"
  by (simp add: ver_def)

lemma ver_inhale:
  "well_defined_assert_set P A \<longleftrightarrow> ver Pr A (Inhale P)"
  by (meson well_defined_assert_set_def v_singleton ver_inhale_single)

lemma union_sum:
  "(\<Union>a\<in>A. {a} \<oplus>\<oplus> B) = A \<oplus>\<oplus> B" (is "?a = ?b")
proof -
  have "?a \<subseteq> ?b"
  proof (rule subsetI)
    fix x assume "x \<in> ?a"
    then obtain a where "a \<in> A" "x \<in> {a} \<oplus>\<oplus> B" by blast
    then show "x \<in> ?b" using sep_algebra.elem_add_set sep_algebra_axioms by fastforce
  qed
  moreover have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix x assume "x \<in> ?b"
    then obtain a b where "a \<in> A" "b \<in> B" "Some x = Some a \<oplus> Some b"
      using set_add_elem by blast
    then show "x \<in> ?a"
      by (metis UN_iff set_add_elem_reci singletonI)
  qed
  ultimately show ?thesis by blast
qed

lemma sem_inhale: 
  assumes "well_defined_assert_set P A"
  shows "sem Pr A (Inhale P) = A \<oplus>\<oplus> Inh P"
  using assms well_defined_assert_set_def union_sum by auto

lemma ver_exhale:
  "ver Pr {\<phi>} (Exhale P) \<longleftrightarrow> (P \<phi> = Some True)" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b"
    by (meson semantics.simps(9) singletonI ver_def)
  moreover have "?b \<Longrightarrow> ?a"
  proof -
    assume "?b"
    then have "well_defined_assert P \<phi>"
      by (simp add: well_defined_assert_def)
    then show ?thesis
      using \<open>P \<phi> = Some True\<close> ver_def by auto
  qed
  ultimately show ?thesis by blast
qed

lemma singleton_sem:
  assumes "ver Pr {\<phi>} s"
  shows "sem Pr {\<phi>} s = get_S (semantics Pr \<phi> s)"
  by simp

lemma sem_exhale:
  assumes "P \<phi> = Some True"
  shows "sem Pr {\<phi>} (Exhale P) = {\<phi>' | \<phi>' i r. Some \<phi> = Some i \<oplus> Some r \<and> i \<in> Inh P \<and> Some \<phi>' = s_core i \<oplus> Some r}"
proof -
  define R where "R = {\<phi>' | \<phi>' i r. Some \<phi> = Some i \<oplus> Some r \<and> i \<in> Inh P \<and> Some \<phi>' = s_core i \<oplus> Some r}"
  have "well_defined_assert P \<phi>"
    by (simp add: assms well_defined_assert_def)
  then have "semantics Pr \<phi> (Exhale P) = S R"
    using assms R_def by simp
  then show ?thesis
    by (simp add: R_def)
qed

lemma sem_skip:
  "(ver Pr A Skip) \<and> (sem Pr A Skip = A)"
proof -
  have "ver Pr A Skip"
    by (simp add: ver_def)
  moreover have "\<And>a. semantics Pr a Skip = S {a}" by simp
  then have "sem Pr A Skip = A" by simp
  then show ?thesis
    using calculation by blast
qed

lemma ver_if:
  "ver Pr A (If s1 s2) = (ver Pr A s1 \<and> ver Pr A s2)"
  using ver_def by auto

lemma sem_if_single:
  assumes "ver Pr {\<phi>} (If s1 s2)"
  shows "sem Pr {\<phi>} (If s1 s2) = sem Pr {\<phi>} s1 \<union> sem Pr {\<phi>} s2"
  by (smt assms get_S.simps(1) semantics.simps(4) singletonI singleton_sem ver_def)

lemma sem_if:
  assumes "ver Pr A (If s1 s2)"
  shows "sem Pr A (If s1 s2) = sem Pr A s1 \<union> sem Pr A s2"
proof -
  have "sem Pr A (If s1 s2) = (\<Union>a\<in>A. sem Pr {a} (If s1 s2))" by simp
  then have "... = (\<Union>a\<in>A. sem Pr {a} s1 \<union> sem Pr {a} s2)"
    by (meson Sup.SUP_cong assms sem_if_single v_singleton)
  then have "... = (\<Union>a\<in>A. sem Pr {a} s1) \<union> (\<Union>a\<in>A. sem Pr {a} s2)"
    by blast
  then show ?thesis
    using \<open>(\<Union>a\<in>A. sem Pr {a} (stmt.If s1 s2)) = (\<Union>a\<in>A. sem Pr {a} s1 \<union> sem Pr {a} s2)\<close> by auto
qed

lemma sem_assume_true:
  assumes "b \<phi> = Some True"
      and "well_defined_assert b \<phi>"
  shows "sem Pr {\<phi>} (Assume b) = {\<phi>}"
  by (simp add: assms(1) assms(2))

lemma sem_assume_false:
  assumes "b \<phi> = Some False"
  shows "sem Pr {\<phi>} (Assume b) = {}"
proof -
  have "ver Pr {\<phi>} (Assume b)" 
    using assms semantics.simps(2) ss.simps(3) ver_def well_defined_assert_def by fastforce
  then show ?thesis 
    by (simp add: assms well_defined_assert_def)
qed

lemma ver_havoc:
  "ver Pr {\<phi>} (Havoc l) \<longleftrightarrow> set l \<subseteq> \<sigma> \<phi>"
  by (metis ver_def semantics.simps(7) singletonD singletonI ss.distinct(1))

lemma sem_havoc:
  assumes "ver Pr {\<phi>} (Havoc l)"
  shows "sem Pr {\<phi>} (Havoc l) = {h_comp \<phi> l} \<oplus>\<oplus> h l"
  using assms ver_havoc by auto

lemma ver_var:
  "ver Pr {\<phi>} (Var x) \<longleftrightarrow> set x \<inter> \<sigma> \<phi> = {}"
  using ver_def by auto

lemma sem_var:
  assumes "ver Pr A (Var x)"
  shows "sem Pr A (Var x) = A \<oplus>\<oplus> h x"
  by (smt Sup.SUP_cong assms get_S.simps(1) v_singleton semantics_algebra_axioms s_singleton semantics.simps(5) singleton_sem union_sum ver_var)

lemma ver_seq_single:
  "ver Pr {\<phi>} (Seq s1 s2) \<longleftrightarrow> ver Pr {\<phi>} s1 \<and> ver Pr (sem Pr {\<phi>} s1) s2" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b"
  proof -
    assume "?a"
    then have "ver Pr {\<phi>} s1"
      using ver_def by auto
    define A where "A = get_S (semantics Pr \<phi> s1)"
    then have "A = sem Pr {\<phi>} s1" by simp
    then have "union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s2) ` A) \<noteq> Error"
      by (smt A_def Sup.SUP_cong \<open>ver Pr {\<phi>} (s1 ; s2)\<close> semantics.simps(3) semantics_algebra_axioms singletonI ver_def)
    then show "?b"
      by (smt \<open>A = sem Pr {\<phi>} s1\<close> \<open>ver Pr {\<phi>} s1\<close> image_iff union_set_ss.simps ver_def)
  qed
  moreover have "?b \<Longrightarrow> ?a"
  proof -
    assume "?b"
    define A where "A = get_S (semantics Pr \<phi> s1)"
    then have "A = sem Pr {\<phi>} s1" by simp
    then have "union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s2) ` A) \<noteq> Error"
      using \<open>ver Pr {\<phi>} s1 \<and> ver Pr (sem Pr {\<phi>} s1) s2\<close> ver_def by auto
    then show "?a"
      by (smt A_def Sup.SUP_cong \<open>ver Pr {\<phi>} s1 \<and> ver Pr (sem Pr {\<phi>} s1) s2\<close> semantics.simps(3) semantics_algebra_axioms singletonD ver_def)
  qed
  ultimately show ?thesis by blast
qed

lemma ver_seq:
  "ver Pr A (Seq s1 s2) \<longleftrightarrow> ver Pr A s1 \<and> ver Pr (sem Pr A s1) s2"
proof -
  have "ver Pr A (Seq s1 s2) \<longleftrightarrow> (\<forall>\<phi>\<in>A. ver Pr {\<phi>} (Seq s1 s2))"
    using v_singleton by blast
  then have "... \<longleftrightarrow> (\<forall>\<phi> \<in> A. ver Pr {\<phi>} s1 \<and> ver Pr (sem Pr {\<phi>} s1) s2)"
    using ver_seq_single by blast
  then have "... \<longleftrightarrow> ver Pr A s1 \<and> ver Pr (sem Pr A s1) s2"
    by (meson elem_sem v_singleton)
  then show ?thesis
    by (simp add: \<open>(\<forall>\<phi>\<in>A. ver Pr {\<phi>} (s1 ; s2)) = (\<forall>\<phi>\<in>A. ver Pr {\<phi>} s1 \<and> ver Pr (sem Pr {\<phi>} s1) s2)\<close> \<open>ver Pr A (s1 ; s2) = (\<forall>\<phi>\<in>A. ver Pr {\<phi>} (s1 ; s2))\<close>)
qed

lemma union_ss:
  assumes "union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s) ` A) = S r"
      and "ver Pr A s"
  shows "r = sem Pr A s"
proof -
  have "sem Pr A s = (\<Union>a\<in>A. sem Pr {a} s)" by simp
  then have "... = (\<Union>a\<in>A. get_S (semantics Pr a s))"
    by auto
  then show ?thesis
    by (metis UN_extend_simps(10) \<open>sem Pr A s = (\<Union>a\<in>A. sem Pr {a} s)\<close> assms(1) get_S.simps(1) ss.distinct(1) union_set_ss.simps)
qed

lemma sem_seq_single:
  assumes "ver Pr {\<phi>} (s1 ; s2)"
  shows "sem Pr {\<phi>} (Seq s1 s2) = sem Pr (sem Pr {\<phi>} s1) s2" (is "?a = ?b")
proof -
  define A where "A = get_S (semantics Pr \<phi> s1)"
  then have "A = sem Pr {\<phi>} s1" by simp
  then have "union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s2) ` A) \<noteq> Error"
    by (smt A_def Sup.SUP_cong \<open>ver Pr {\<phi>} (s1 ; s2)\<close> semantics.simps(3) semantics_algebra_axioms singletonI ver_def)
  then have "union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s2) ` A) = S (sem Pr {\<phi>} (s1 ; s2))"
  proof -
    have "semantics Pr \<phi> (s1 ; s2) = union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s2) ` A)"
      by (smt A_def Sup.SUP_cong assms semantics.simps(3) semantics_algebra_axioms singletonI ver_def)
    then show ?thesis
      using \<open>union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s2) ` A) \<noteq> Error\<close> by auto
  qed
  then show ?thesis
    by (metis UN_extend_simps(10) \<open>A = sem Pr {\<phi>} s1\<close> \<open>union_set_ss ((\<lambda>\<phi>'. semantics Pr \<phi>' s2) ` A) \<noteq> Error\<close> get_S.simps(1) sem.simps union_set_ss.simps)
qed

lemma sem_seq:
  assumes "ver Pr A (s1 ; s2)"
  shows "sem Pr A (Seq s1 s2) = sem Pr (sem Pr A s1) s2"
proof -
  have "sem Pr A (Seq s1 s2) = (\<Union>a\<in>A. sem Pr {a} (Seq s1 s2))"
    by auto
  then have "... = (\<Union>a\<in>A. sem Pr (sem Pr {a} s1) s2)"
    by (meson Sup.SUP_cong assms sem_seq_single v_singleton)
  then have "... = sem Pr (\<Union>a\<in>A. sem Pr {a} s1) s2"
    by simp
  then show ?thesis
    using \<open>(\<Union>a\<in>A. sem Pr {a} (s1 ; s2)) = (\<Union>a\<in>A. sem Pr (sem Pr {a} s1) s2)\<close> by auto
qed

lemma rename_set_empty:
  assumes "wf_renaming t"
  shows "rename_set {u} t = {u}" (is "?a = ?b")
proof -
  have "?a \<subseteq> ?b" using rename_state_neutral assms by simp
  moreover have "?b \<subseteq> ?a" using calculation by auto
  ultimately show ?thesis by blast
qed

lemma store_same_pred_supp_inhale:
  assumes "wf_assert P"
      and "ver Pr {a} (Inhale P)"
      and "b \<in> sem Pr {a} (Inhale P)"
    shows "\<sigma> b = \<sigma> a"
proof -
  have "b \<in> {a} \<oplus>\<oplus> Inh P"
    using assms(2) assms(3) sem_inhale ver_inhale by blast
  then obtain i where "i \<in> Inh P" "Some b = Some a \<oplus> Some i"
    using set_add_elem by fastforce
  moreover have "well_defined_assert P a"
    using assms(2) ver_inhale_single by auto
  then have "\<And>i. i\<in>Inh P \<Longrightarrow> a ## i \<Longrightarrow> \<sigma> i \<subseteq> \<sigma> a" 
    using assms(1) wf_assert_def by blast
  then have "\<sigma> i \<subseteq> \<sigma> a"
    by (metis calculation(1) calculation(2) defined_def is_none_code(2))
  then show ?thesis
    using calculation(2) store_add by blast
qed

lemma exhale_verif:
  assumes "ver Pr {\<phi>} (Exhale P)"
    shows "P \<phi> = Some True"
  using assms(1) ver_exhale by metis

lemma exhale_sem_inh:
  assumes "i \<in> Inh P"
      and "Some \<phi> = Some i \<oplus> Some r"
      and "ver Pr {\<phi>} (Exhale P)"
    shows "{the (s_core i \<oplus> Some r)} \<subseteq> sem Pr {\<phi>} (Exhale P)"
proof -
  have "core i ## r"
    by (metis assms(2) core_properties(1) core_properties(2) defined_trans_plus pure_smaller_ok)
  then obtain cir where "Some cir = s_core i \<oplus> Some r"
    by (metis assms(2) associative commutative decompo_new_plus option.collapse option.discI plus.simps(2))
  then have "the (s_core i \<oplus> Some r) = cir" by (metis option.sel)
  have def: "sem Pr {\<phi>} (Exhale P) = {\<phi>' | \<phi>' i r. Some \<phi> = Some i \<oplus> Some r \<and> i \<in> Inh P \<and> Some \<phi>' = s_core i \<oplus> Some r}"
    using assms(3) exhale_verif sem_exhale by blast
  then have inc: "cir \<in> sem Pr {\<phi>} (Exhale P)"
    using \<open>Some cir = s_core i \<oplus> Some r\<close> assms(2) assms(1) by blast
  then show ?thesis using \<open>the (s_core i \<oplus> Some r) = cir\<close> def empty_iff inc subset_singletonD by auto
qed

lemma greaterI:
  "(\<And>y. y \<in> A \<Longrightarrow> (\<exists>x \<in> B. x << y)) \<Longrightarrow> A >> B"
  by (simp add: bigger_set_def)

lemma exhale_sem_bigger_core:
  assumes "i \<in> Inh P"
      and "wf_assert P"
  shows "sem Pr {i} (Exhale P) >> { |i| }"
proof (rule greaterI)
  fix y assume "y \<in> sem Pr {i} (Exhale P)"
  have "ver Pr {i} (Exhale P)"
    using assms(1) assms(2) subset_smaller ver_exhale wf_assert_def by auto
  then have "y \<in> {yy. \<exists>\<phi>' ia r. yy = \<phi>' \<and> Some i = Some ia \<oplus> Some r \<and> ia \<in> Inh P \<and> Some \<phi>' = s_core ia \<oplus> Some r}"
    using \<open>y \<in> sem Pr {i} (Exhale P)\<close> exhale_verif mem_Collect_eq semantics_algebra.sem_exhale semantics_algebra_axioms by fastforce
  then obtain ia r where "Some i = Some ia \<oplus> Some r" "ia \<in> Inh P" "Some y = s_core ia \<oplus> Some r"
    by blast
  then have "|i| << y"
    by (metis associative core_add decompo_new_plus s_C_def s_core_def smaller_def)
  then show "\<exists>x\<in>{|i|}. x << y"
    by blast
qed

lemma exhale_sem_bigger_core_bigger:
  assumes "i \<in> Inh P"
      and "wf_assert P"
      and "i << x"
  shows "sem Pr {x} (Exhale P) >> { |x| }"
proof (rule greaterI)
  fix y assume "y \<in> sem Pr {x} (Exhale P)"
  have "ver Pr {x} (Exhale P)" 
    using assms(1) assms(2) assms(3) bigger_set_def ver_exhale wf_assert_def by auto
  then have "y \<in> {yy. \<exists>\<phi>' ia r. yy = \<phi>' \<and> Some x = Some ia \<oplus> Some r \<and> ia \<in> Inh P \<and> Some \<phi>' = s_core ia \<oplus> Some r}"
    using \<open>y \<in> sem Pr {x} (Exhale P)\<close> exhale_verif mem_Collect_eq semantics_algebra.sem_exhale semantics_algebra_axioms by fastforce
  then obtain ia r where "Some x = Some ia \<oplus> Some r" "ia \<in> Inh P" "Some y = s_core ia \<oplus> Some r"
    by blast
  then have "|x| << y"
    by (metis associative core_add decompo_new_plus s_C_def s_core_def smaller_def)
  then show "\<exists>z\<in>{|x|}. z << y"
    by blast
qed



(*
lemma exhale_sem_bigger_core_framing:
  assumes "i \<in> Inh P"
      and "wf_assert P"
      and "framing Pr A (Exhale P)"
      and "
  shows "sem Pr {i} (Exhale P) >> { |i| }"
*)

lemma store_same_pred_supp_exhale:
  assumes "ver Pr {a} (Exhale P)"
      and "b \<in> sem Pr {a} (Exhale P)"
    shows "\<sigma> b = \<sigma> a"
proof -
  have "P a = Some True"
    using assms(1) exhale_verif by blast
  moreover have "sem Pr {a} (Exhale P) =
    {\<phi>' |\<phi>' i r. Some a = Some i \<oplus> Some r \<and> i \<in> Inh P \<and> Some \<phi>' = s_core i \<oplus> Some r}"
    using calculation sem_exhale by auto
  then obtain r i where "i \<in> Inh P" "Some b = s_core i \<oplus> Some r" "Some a = Some i \<oplus> Some r"
    by (smt CollectD assms(2))
  then show ?thesis
    using s_core_def store_add store_pure by auto
qed

lemma modif_in_read: "set (modif s) \<subseteq> set (read s)"
proof (induct rule: modif.induct)
  case (11 s)
  then show ?case
    by (simp add: modif_other_read_other)
qed (auto)

lemma rename_modif_list:
  assumes "wf_renaming t"
  shows "modif (rename s t) = rename_list (modif s) t"
proof (induction rule: rename.induct)
  case (10 other t)
  then show ?case
    by (simp add: modif_rename_other rename_list_def)
qed (auto simp add: rename_list_def)

lemma rename_modif_no_inter_elem: "wf_renaming t \<and> set l \<inter> set (modif s) = {}
          \<Longrightarrow> set (rename_list l t) \<inter> set (modif (rename s t)) = {}" (is "?a \<Longrightarrow> ?b")
proof -
  assume "?a"
  let ?r = "\<lambda>elem. rename_elem elem t"
  have "set (rename_list l t) = ?r ` (set l)"
    using rename_list_def by auto
  moreover have "set (modif (rename s t)) = ?r ` (set (modif s))"
    by (simp add: \<open>wf_renaming t \<and> set l \<inter> set (modif s) = {}\<close> rename_list_def rename_modif_list)
  ultimately show "?b"
    by (smt \<open>wf_renaming t \<and> set l \<inter> set (modif s) = {}\<close> disjoint_iff_not_equal image_iff rename_inv_def_elem)
qed

lemma rename_store_inv: "wf_renaming t \<and> set (modif (rename s t)) \<inter> \<sigma> (rename_state r t) = {} \<Longrightarrow> set (modif s) \<inter> \<sigma> r = {}" (is "?a \<Longrightarrow> ?b")
proof -
  assume "?a"
  let ?r = "\<lambda>elem. rename_elem elem t"
  have "set (modif (rename s t)) = ?r ` (set (modif s))"
    using rename_modif_list
    by (simp add: \<open>wf_renaming t \<and> set (modif (rename s t)) \<inter> \<sigma> (rename_state r t) = {}\<close> rename_list_def)
  moreover have "\<sigma> (rename_state r t) = ?r ` (\<sigma> r)"
    using \<open>wf_renaming t \<and> set (modif (rename s t)) \<inter> \<sigma> (rename_state r t) = {}\<close> rename_store by auto
  ultimately show "?b"
    using \<open>wf_renaming t \<and> set (modif (rename s t)) \<inter> \<sigma> (rename_state r t) = {}\<close> by blast
qed

lemma rename_modif_no_inter:
  assumes "wf_renaming (args @ ret, x @ y, l, do)"
      and "length args = length x"
      and "set args \<inter> set (modif s) = {}"
      and "set (modif s) \<subseteq> set do"
    shows "set x \<inter> set (modif (rename s (args @ ret, x @ y, l, do))) = {}"
proof -
  let ?t = "(args @ ret, x @ y, l, do)"
  have "rename_list args ?t = x" 
    by (smt append_eq_append_conv assms(1) assms(2) rename_list_concat rename_list_same rename_list_same_length)
  then show ?thesis
    by (metis assms(1) assms(3) rename_modif_no_inter_elem)
qed

lemma rename_store_lemma: "wf_renaming t \<Longrightarrow> set (modif (rename s t)) \<inter> \<sigma> r = {} \<Longrightarrow> set (modif s) \<inter> \<sigma> (rename_state r (rename_inv t)) = {}"
  by (metis rename_inv_def_state rename_store_inv renaming_invert_wf)

lemma rename_removes_vars:
  "wf_renaming (l1, l2, l3, do) \<and> set (read s) \<subseteq> set do \<longrightarrow> set (read (rename s (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3) \<subseteq> set l2"
proof (induct rule: read.induct[of "\<lambda>s. wf_renaming (l1, l2, l3, do) \<and> set (read s) \<subseteq> set do \<longrightarrow> set (read (rename s (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3) \<subseteq> set l2"])
  case (3 y m x)
  then show ?case
    by (metis read.simps(3) rename.simps(8) rename_list_concat semantics_algebra.rename_removes_vars_list semantics_algebra_axioms)
next
  case (4 b I s)
  let ?t = "(l1, l2, l3, do)"
  have "set (read (rename (While b I s) ?t)) = set (read (rename s ?t)) \<union> set (read_pred (rename_pred b ?t)) \<union> set (read_pred (rename_pred I ?t))"
    by auto
  then show ?case
    by (simp add: "4.hyps" Int_Un_distrib2 rename_removes_vars_pred)
next
  case (5 b)
  then show ?case
    by (simp add: rename_removes_vars_pred)
next
  case (6 P)
  then show ?case
    by (simp add: rename_removes_vars_pred)
next
  case (7 P)
  then show ?case
    by (simp add: rename_removes_vars_pred)
next
  case (8 l)
  then show ?case
    by (simp add: rename_removes_vars_list)
next
  case (9 l)
  then show ?case
    by (simp add: rename_removes_vars_list)
next
  case (11 s)
  then show ?case
    by (simp add: rename_removes_vars_other)
qed (auto)

lemma rename_removes_vars_modif:
  "wf_renaming (l1, l2, l3, do) \<and> set (modif s) \<subseteq> set do \<longrightarrow> set (modif (rename s (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3) \<subseteq> set l2"
proof (induct rule: read.induct[of "\<lambda>s. wf_renaming (l1, l2, l3, do) \<and> set (modif s) \<subseteq> set do \<longrightarrow> set (modif (rename s (l1, l2, l3, do))) \<inter> (set l1 \<union> set l3) \<subseteq> set l2"])
  case (3 y m x)
  then show ?case 
    by (simp add: rename_removes_vars_list)
next
  case (4 b I s)
  let ?t = "(l1, l2, l3, do)"
  have "set (read (rename (While b I s) ?t)) = set (read (rename s ?t)) \<union> set (read_pred (rename_pred b ?t)) \<union> set (read_pred (rename_pred I ?t))"
    by auto
  then show ?case
    by (simp add: "4.hyps" Int_Un_distrib2 rename_removes_vars_pred)
next
  case (5 b)
  then show ?case
    by (simp add: rename_removes_vars_pred)
next
  case (6 P)
  then show ?case
    by (simp add: rename_removes_vars_pred)
next
  case (7 P)
  then show ?case
    by (simp add: rename_removes_vars_pred)
next
  case (8 l)
  then show ?case
    by (simp add: rename_removes_vars_list)
next
  case (9 l)
  then show ?case
    by (simp add: rename_removes_vars_list)
next
  case (11 s)
  then show ?case 
    using rename_modif_list rename_removes_vars_list by presburger
qed (auto)

lemma rename_list_inv:
  assumes "wf_renaming t"
  shows "rename_list (rename_list l t) (rename_inv t) = l"
  apply (induction l)
  apply (simp add: rename_list_def)
  by (simp add: assms rename_inv_def_elem rename_list_def)

lemma renaming_invert:
  "wf_renaming t \<longrightarrow> rename (rename s t) (rename_inv t) = s"
proof (induct rule: rename.induct[of "\<lambda>s t. wf_renaming t \<longrightarrow> rename (rename s t) (rename_inv t) = s"])
case (1 P t)
  then show ?case
    by (simp add: rename_inv_def_pred)
next
  case (2 P t)
  then show ?case
    using rename_inv_def_pred by auto
next
  case (4 x t)
  then show ?case
    by (simp add: rename_list_inv)
next
  case (5 x t)
  then show ?case
    by (simp add: rename_list_inv)
next
  case (7 b I s t)
  then show ?case
    by (simp add: rename_inv_def_pred)
next
  case (8 y m x t)
  then show ?case by (simp add: rename_list_inv)
next
  case (9 b t)
  then show ?case 
    by (simp add: rename_inv_def_pred)
next
  case (10 other t)
  then show ?case
    by (simp add: rename_inv_def_other)
qed (simp_all)

lemma member_rename_set_inv:
  assumes "wf_renaming t"
  shows "rename_state x (rename_inv t) \<in> A \<longleftrightarrow> x \<in> rename_set A t"
  by (smt assms image_iff rename_inv_def_state rename_set.simps renaming_invert_wf)

lemma h_rename_set:
  assumes "wf_renaming t"
  shows "h (rename_list V t) = rename_set (h V) t" (is "?a = ?b")
proof -
  let ?t = "rename_inv t"
  have "?a \<subseteq> ?b"
  proof (rule subsetI)
    fix x 
    let ?x = "rename_state x ?t"
    assume "x \<in> ?a"
    then have "?x \<in> h V"
      by (smt assms h_def image_set mem_Collect_eq pure_def rename_list_def rename_list_inv rename_state_add rename_store renaming_invert_wf)
    then show "x \<in> ?b"
      using assms member_rename_set_inv by blast
  qed
  moreover have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix x
    let ?x = "rename_state x ?t"
    assume "x \<in> ?b"
    then have "?x \<in> h V"
      using assms member_rename_set_inv by blast
    then show "x \<in> ?a"
      using assms image_set mem_Collect_eq pure_def rename_list_def rename_state_add rename_store renaming_invert_wf semantics_algebra.h_def semantics_algebra.rename_inv_def_state semantics_algebra_axioms
      by smt
  qed
  ultimately show ?thesis by blast
qed

lemma rename_set_add:
  assumes "wf_renaming t"
  shows "rename_set (A \<oplus>\<oplus> B) t = rename_set A t \<oplus>\<oplus> rename_set B t" (is "?A = ?B")
proof -
  let ?t = "rename_inv t"
  have "?A \<subseteq> ?B"
  proof (rule subsetI)
    fix x
    let ?x = "rename_state x ?t"
    assume "x \<in> ?A"
    then have "?x \<in> A \<oplus>\<oplus> B"
      using assms member_rename_set_inv by blast
    then obtain a b where "a \<in> A" "b \<in> B" "Some ?x = Some a \<oplus> Some b"
      using set_add_elem by blast
    then have "Some x = Some (rename_state a t) \<oplus> Some (rename_state b t)"
      by (smt Set.set_insert \<open>x \<in> rename_set (A \<oplus>\<oplus> B) t\<close> assms image_insert insertE member_rename_set_inv rename_set.simps rename_state_add)
    then show "x \<in> ?B"
      using \<open>a \<in> A\<close> \<open>b \<in> B\<close> elem_add_set by auto
  qed
  moreover have "?B \<subseteq> ?A"
  proof (rule subsetI)
    fix x assume "x \<in> ?B"
    then obtain a b where "a \<in> A" "b \<in> B" "Some x = Some (rename_state a t) \<oplus> Some (rename_state b t)"
      using elem_add_set by auto
    then show "x \<in> ?A"
    proof -
      obtain aa :: 'a and aaa :: 'a where
f1: "(Some x = Some (rename_state aa t) \<oplus> Some (rename_state aaa t) \<and> aaa \<in> B) \<and> aa \<in> A"
        by (meson \<open>\<And>thesis. (\<And>a b. \<lbrakk>a \<in> A; b \<in> B; Some x = Some (rename_state a t) \<oplus> Some (rename_state b t)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
      then have "Some (rename_state x (rename_inv t)) = Some (rename_state (rename_state aa t) (rename_inv t)) \<oplus> Some (rename_state (rename_state aaa t) (rename_inv t))"
        by (meson assms renaming_invert_wf semantics_algebra.rename_state_add semantics_algebra_axioms)
      then show ?thesis
        using f1 by (metis (no_types) assms elem_add_set member_rename_set_inv rename_inv_def_state)
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma h_comp_c_same:
  "C (h_comp x l) = C x"
  by (smt c_add h_comp_some_exists h_comp_some_sum neutral option.sel properties_c(2) pure_c sep_algebra.s_C_def sep_algebra_axioms)

lemma wf_renaming_rename_list_set:
  assumes "wf_renaming t"
      and "set A = set B - set D"
    shows "set (rename_list A t) = set (rename_list B t) - set (rename_list D t)" (is "?a = ?b")
proof -
  have "?a \<subseteq> ?b"
  proof (rule subsetI)
    fix x assume "x \<in> ?a"
    then obtain i where "i < length A" "x = rename_elem (A ! i) t"
      by (metis assms(1) in_set_conv_nth rename_elem_list rename_list_same_length)
    then obtain "A ! i \<in> set B" "A ! i \<notin> set D"
      using assms(2) nth_mem by auto
    then show "x \<in> ?b"
      by (metis Diff_iff \<open>x = rename_elem (A ! i) t\<close> assms(1) in_set_conv_nth rename_elem_list rename_inv_def_elem rename_list_same_length)
  qed
  moreover have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix x assume "x \<in> ?b"
    then obtain j where "x \<notin> set (rename_list D t)" "j < length B" "x = rename_elem (B ! j) t"
      by (metis Diff_iff assms(1) in_set_conv_nth rename_elem_list rename_list_same_length)
    then have "B ! j \<notin> set D"
      by (metis assms(1) in_set_conv_nth rename_elem_list rename_list_same_length)
    then have "B ! j \<in> set A"
      by (simp add: \<open>j < length B\<close> assms(2))
    then show "x \<in> ?a"
      by (metis \<open>x = rename_elem (B ! j) t\<close> assms(1) in_set_conv_nth rename_elem_list rename_list_same_length)
  qed
  ultimately show ?thesis by blast
qed

lemma h_comp_rename:
  assumes "wf_renaming t"
  shows "h_comp (rename_state \<phi> t) (rename_list V t) = rename_state (h_comp \<phi> V) t" (is "?a = ?b")
proof -
  have "C ?a = C ?b"
    by (simp add: assms h_comp_c_same rename_state_c_same)
  moreover have "|?a| = |?b|"
  proof -
    let ?V = "rename_list V t"
    have "\<sigma> |?a| = \<sigma> |?b|"
    proof -
      obtain sigma where "set sigma = \<sigma> \<phi>"
        by (meson finite_list finite_store)
      then have "\<sigma> (rename_state \<phi> t) = set (rename_list sigma t)"
        by (simp add: assms rename_list_def rename_store)
      then have "\<sigma> |?a| = set (rename_list sigma t) - set ?V"
        using h_comp_store store_pure by auto
      moreover obtain sigma_bis where "set sigma_bis = \<sigma> (h_comp \<phi> V)"
        by (meson finite_list finite_store)
      then have "\<sigma> |?b| = set (rename_list sigma_bis t)"
        using assms rename_list_def rename_store store_pure by auto
      moreover have "set sigma_bis = set sigma - set V"
        by (simp add: \<open>set sigma = \<sigma> \<phi>\<close> \<open>set sigma_bis = \<sigma> (h_comp \<phi> V)\<close> h_comp_store)
      ultimately show ?thesis
        by (simp add: assms wf_renaming_rename_list_set)
    qed
    moreover have "|?a| << rename_state \<phi> t"
    proof -
      have "rename_state \<phi> t << rename_state \<phi> t"
        using smaller_refl by blast
      then have "?a << rename_state \<phi> t"
        by (metis h_comp_sum commutative_monoid.s_core_def commutative_monoid_axioms smaller_def)
      then show ?thesis
        using core_properties(2) smaller_trans by blast
    qed
    moreover have "|?b| << rename_state \<phi> t"
    proof -
      have "h_comp \<phi> V << \<phi>"
        using h_comp_sum commutative_monoid.s_core_def commutative_monoid.smaller_def commutative_monoid_axioms by fastforce
      then have "?b << rename_state \<phi> t"
        by (simp add: assms wf_renaming_order)
      then show ?thesis
        using core_properties(2) smaller_trans by blast
    qed
    ultimately show ?thesis
      by (metis core_properties(1) pure_is_exactly_store pure_is_exactly_store_variant set_eq_subset)
  qed
  ultimately show ?thesis
    using properties_c(1) by blast
qed

lemma wf_core_rename_same:
  assumes "wf_renaming t"
  shows "rename_state ( |x| ) t = | rename_state x t |"
proof -
  have "\<sigma> (rename_state ( |x| ) t) = \<sigma> | rename_state x t |"
    using assms rename_store store_pure by auto
  moreover have "pure (rename_state ( |x| ) t)"
    by (metis assms core_properties(1) pure_def rename_state_add)
  moreover have "rename_state ( |x| ) t << rename_state x t"
    using assms decompo rename_state_add smaller_def by blast
  ultimately show ?thesis
    by (metis core_properties(1) core_properties(2) semantics_algebra.pure_is_exactly_store semantics_algebra.pure_is_exactly_store_variant semantics_algebra_axioms set_eq_subset)
qed

definition rename_sem_property :: "('a, 'b, 'c) program \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> 'b rename_t \<Rightarrow> bool" where
  "rename_sem_property Pr s t \<longleftrightarrow> (\<forall>\<phi>. wf_renaming t \<and> wf_stmt Pr s \<and> wf_program Pr \<and> ver Pr {\<phi>} s \<longrightarrow>
    ver Pr {rename_state \<phi> t} (rename s t) \<and> sem Pr {rename_state \<phi> t} (rename s t) = rename_set (sem Pr {\<phi>} s) t)"

lemma rename_sem_inhale:
  assumes "wf_renaming t"
      and "ver Pr {\<phi>} (Inhale P)"
      and "wf_assert P"
    shows "ver Pr {rename_state \<phi> t} (rename (Inhale P) t)"
      and "sem Pr {rename_state \<phi> t} (rename (Inhale P) t) = rename_set (sem Pr {\<phi>} (Inhale P)) t"
proof -
  show "ver Pr {rename_state \<phi> t} (rename (Inhale P) t)" 
    by (metis assms(1) assms(2) assms(3) rename.simps(1) semantics_algebra.well_defined_assert_rename semantics_algebra_axioms ver_inhale_single)
  moreover have "sem Pr {rename_state \<phi> t} (rename (Inhale P) t) = rename_set (sem Pr {\<phi>} (Inhale P)) t"
  proof -
    have "sem Pr {rename_state \<phi> t} (rename (Inhale P) t) = {rename_state \<phi> t} \<oplus>\<oplus> Inh (rename_pred P t)"
      using calculation ver_inhale_single by auto
    moreover have "... = {rename_state \<phi> t} \<oplus>\<oplus> rename_set (Inh P) t"
      using assms(1) inh_renamed by blast
    moreover have "... = rename_set ({\<phi>} \<oplus>\<oplus>  Inh P) t" (is "?a = ?b")
      using assms rename_set_add by auto
    ultimately show ?thesis
      using assms sem_inhale ver_inhale by force
  qed
  ultimately show "sem Pr {rename_state \<phi> t} (rename (Inhale P) t) = rename_set (sem Pr {\<phi>} (Inhale P)) t" by blast
qed

lemma rename_sem_assume:
  assumes "wf_renaming t"
      and "ver Pr {\<phi>} (Assume b)"
    shows "ver Pr {rename_state \<phi> t} (rename (Assume b) t)"
      and "sem Pr {rename_state \<phi> t} (rename (Assume b) t) = rename_set (sem Pr {\<phi>} (Assume b)) t"
proof -
  show "ver Pr {rename_state \<phi> t} (rename (Assume b) t)"
    by (metis assms well_defined_assert_rename semantics.simps(2) semantics_algebra.rename.simps(9) semantics_algebra.ver_def semantics_algebra_axioms singletonD singletonI ss.distinct(1))
  then have "sem Pr {rename_state \<phi> t} (rename (Assume b) t) = rename_set (sem Pr {\<phi>} (Assume b)) t"
    by (smt assms(1) assms(2) image_empty image_insert rename.simps(9) rename_pred_same semantics.simps(2) semantics_algebra.rename_set.simps semantics_algebra_axioms singletonI singleton_semantics ver_def)
  then show "sem Pr {rename_state \<phi> t} (rename (Assume b) t) = rename_set (sem Pr {\<phi>} (Assume b)) t"
    using \<open>ver Pr {rename_state \<phi> t} (rename (Assume b) t)\<close> by blast
qed

lemma rename_sem_exhale:
  assumes "wf_renaming t"
      and "ver Pr {\<phi>} (Exhale P)"
    shows "ver Pr {rename_state \<phi> t} (rename (Exhale P) t)"
      and "sem Pr {rename_state \<phi> t} (rename (Exhale P) t) = rename_set (sem Pr {\<phi>} (Exhale P)) t"
proof -
  let ?\<phi> = "rename_state \<phi> t"
  let ?P = "rename_pred P t"
  show "ver Pr {rename_state \<phi> t} (rename (Exhale P) t)"
    by (metis assms(1) assms(2) exhale_verif rename.simps(2) semantics_algebra.rename_pred_same semantics_algebra.ver_exhale semantics_algebra_axioms)
  then show "sem Pr {rename_state \<phi> t} (rename (Exhale P) t) = rename_set (sem Pr {\<phi>} (Exhale P)) t" (is "?a = ?b")
  proof -
    have "?a \<subseteq> ?b"
    proof (rule subsetI)
      fix x assume "x \<in> ?a"
      then obtain i r where "i \<in> Inh ?P" "Some ?\<phi> = Some i \<oplus> Some r" "Some x = s_core i \<oplus> Some r"
        using \<open>ver Pr {rename_state \<phi> t} (rename (Exhale P) t)\<close> ver_exhale sem_exhale by auto
      then have "rename_state i (rename_inv t) \<in> Inh P"
        using assms inh_renamed member_rename_set_inv by blast
      moreover have "Some (rename_state x (rename_inv t)) = Some (rename_state |i| (rename_inv t)) \<oplus> Some (rename_state r (rename_inv t))"
        by (metis \<open>Some x = s_core i \<oplus> Some r\<close> assms commutative_monoid.s_core_def commutative_monoid_axioms rename_state_add semantics_algebra.renaming_invert_wf semantics_algebra_axioms)
      moreover have "rename_state |i| (rename_inv t) = | (rename_state i (rename_inv t)) |"
        by (simp add: assms renaming_invert_wf wf_core_rename_same)
      moreover have "Some \<phi> = Some (rename_state i (rename_inv t)) \<oplus> Some (rename_state r (rename_inv t))"
        by (metis \<open>Some (rename_state \<phi> t) = Some i \<oplus> Some r\<close> assms(1) rename_inv_def_state rename_state_add semantics_algebra.renaming_invert_wf semantics_algebra_axioms)
      ultimately have "rename_state x (rename_inv t) \<in> sem Pr {\<phi>} (Exhale P)"
        using assms exhale_verif s_core_def
        by (smt mem_Collect_eq semantics_algebra.sem_exhale semantics_algebra_axioms)
      then show "x \<in> ?b"
        using \<open>rename_state x (rename_inv t) \<in> sem Pr {\<phi>} (Exhale P)\<close> assms member_rename_set_inv by blast
    qed
    moreover have "?b \<subseteq> ?a"
    proof (rule subsetI)
      fix x
      let ?x = "rename_state x (rename_inv t)"
      assume "x \<in> ?b"
      then have "?x \<in> sem Pr {\<phi>} (Exhale P)"
        using assms member_rename_set_inv by blast
      then obtain i r where "i \<in> Inh P" "Some ?x = s_core i \<oplus> Some r" "Some \<phi> = Some i \<oplus> Some r"
        by (smt assms exhale_verif mem_Collect_eq semantics_algebra.sem_exhale semantics_algebra_axioms)
      then have "Some ?\<phi> = Some (rename_state i t) \<oplus> Some (rename_state r t)"
        using assms rename_state_add by blast
      moreover have "Some x = Some (rename_state |i| t) \<oplus> Some (rename_state r t)"
        by (metis \<open>Some (rename_state x (rename_inv t)) = s_core i \<oplus> Some r\<close> assms rename_inv_def_state rename_state_add s_core_def semantics_algebra.renaming_invert_wf semantics_algebra_axioms)
      moreover have "rename_state i t \<in> Inh ?P"
        by (metis (mono_tags) \<open>i \<in> Inh P\<close> assms(1) image_iff inh_renamed rename_set.simps)
      moreover have "rename_state |i| t = | rename_state i t |"
        by (simp add: assms wf_core_rename_same)
      ultimately show "x \<in> ?a"
        using \<open>ver Pr {rename_state \<phi> t} (rename (Exhale P) t)\<close> mem_Collect_eq rename.simps(2) s_core_def ver_exhale
        by (smt get_S.simps(1) semantics.simps(9) semantics_algebra.ver_def semantics_algebra_axioms singletonI singleton_sem)
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma rename_sem_havoc:
  assumes "wf_renaming t"
      and "ver Pr {\<phi>} (Havoc V)"
    shows "ver Pr {rename_state \<phi> t} (rename (Havoc V) t)"
      and "sem Pr {rename_state \<phi> t} (rename (Havoc V) t) = rename_set (sem Pr {\<phi>} (Havoc V)) t"
proof -
  show "ver Pr {rename_state \<phi> t} (rename (Havoc V) t)"
    using assms image_Un le_iff_sup modif.simps(9) rename.simps(5) rename_modif_list rename_store ver_havoc
    using rename_list_def by auto
  show "sem Pr {rename_state \<phi> t} (rename (Havoc V) t) = rename_set (sem Pr {\<phi>} (Havoc V)) t"
  proof -
    have "sem Pr {rename_state \<phi> t} (rename (Havoc V) t) = {h_comp (rename_state \<phi> t) (rename_list V t)} \<oplus>\<oplus> h (rename_list V t)"
      using \<open>ver Pr {rename_state \<phi> t} (rename (Havoc V) t)\<close> sem_havoc by auto
    moreover have "{h_comp (rename_state \<phi> t) (rename_list V t)} = {rename_state (h_comp \<phi> V) t}"
      using assms h_comp_rename by blast
    moreover have "h (rename_list V t) = rename_set (h V) t"
      using assms h_rename_set by blast
    ultimately have "sem Pr {rename_state \<phi> t} (rename (Havoc V) t) = rename_set ({h_comp \<phi> V} \<oplus>\<oplus> h V) t"
      using assms rename_set_add by auto
    then show ?thesis
      using assms sem_havoc by auto
  qed
qed

lemma rename_sem_var:
  assumes "wf_renaming t"
      and "ver Pr {\<phi>} (Var V)"
    shows "ver Pr {rename_state \<phi> t} (rename (Var V) t)"
      and "sem Pr {rename_state \<phi> t} (rename (Var V) t) = rename_set (sem Pr {\<phi>} (Var V)) t"
proof -
  show "ver Pr {rename_state \<phi> t} (rename (Var V) t)"
    by (metis assms modif.simps(8) rename.simps(4) rename_inv_def_state rename_store_inv semantics_algebra.renaming_invert semantics_algebra.renaming_invert_wf semantics_algebra_axioms ver_var)
  then show "sem Pr {rename_state \<phi> t} (rename (Var V) t) = rename_set (sem Pr {\<phi>} (Var V)) t"
    using h_rename_set[of t V] rename_set_add
    by (metis (no_types, lifting) assms image_insert image_is_empty rename_set.simps sem_var semantics_algebra.rename.simps(4) semantics_algebra_axioms)
qed

lemma rename_sem_seq:
  assumes "wf_renaming t"
      and "ver Pr {\<phi>} (s1 ; s2)"
      and "wf_stmt Pr (s1 ; s2)"
      and "wf_program Pr"
      and "\<And>\<phi>. wf_stmt Pr s1 \<Longrightarrow> wf_program Pr \<Longrightarrow> ver Pr {\<phi>} s1 \<Longrightarrow> ver Pr {rename_state \<phi> t} (rename s1 t) \<and> sem Pr {rename_state \<phi> t} (rename s1 t) = rename_set (sem Pr {\<phi>} s1) t"
      and "\<And>\<phi>. wf_stmt Pr s2 \<Longrightarrow> wf_program Pr \<Longrightarrow> ver Pr {\<phi>} s2 \<Longrightarrow> ver Pr {rename_state \<phi> t} (rename s2 t) \<and> sem Pr {rename_state \<phi> t} (rename s2 t) = rename_set (sem Pr {\<phi>} s2) t"
    shows "ver Pr {rename_state \<phi> t} (rename (s1 ; s2) t)"
      and "sem Pr {rename_state \<phi> t} (rename (s1 ; s2) t) = rename_set (sem Pr {\<phi>} (s1 ; s2)) t"
proof -
  have "ver Pr {rename_state \<phi> t} (rename s1 t) \<and> sem Pr {rename_state \<phi> t} (rename s1 t) = rename_set (sem Pr {\<phi>} s1) t"
    using assms ver_seq by simp
  moreover have "\<And>\<phi>'. \<phi>' \<in> sem Pr {\<phi>} s1 \<Longrightarrow> ver Pr {rename_state \<phi>' t} (rename s2 t) \<and> sem Pr {rename_state \<phi>' t} (rename s2 t) = rename_set (sem Pr {\<phi>'} s2) t"
    by (meson assms(2) assms(3) assms(4) assms(6) semantics_algebra.wf_stmt.simps(1) semantics_algebra_axioms v_singleton ver_seq)
  ultimately show "ver Pr {rename_state \<phi> t} (rename (s1 ; s2) t)"
    by (smt image_iff rename.simps(3) semantics_algebra.rename_set.simps semantics_algebra_axioms v_singleton ver_seq)
  show "sem Pr {rename_state \<phi> t} (rename (s1 ; s2) t) = rename_set (sem Pr {\<phi>} (s1 ; s2)) t" (is "?a = ?b")
  proof -
    have "?a \<subseteq> ?b"
    proof (rule subsetI)
      fix x assume "x \<in> ?a"
      then obtain y where "x \<in> sem Pr {y} (rename s2 t)" "y \<in> sem Pr {rename_state \<phi> t} (rename s1 t)"
        using \<open>ver Pr {rename_state \<phi> t} (rename (s1 ; s2) t)\<close> sem_seq_single by auto
      then show "x \<in> ?b"
        using \<open>\<And>\<phi>'. \<phi>' \<in> sem Pr {\<phi>} s1 \<Longrightarrow> ver Pr {rename_state \<phi>' t} (rename s2 t) \<and> sem Pr {rename_state \<phi>' t} (rename s2 t) = rename_set (sem Pr {\<phi>'} s2) t\<close> \<open>ver Pr {rename_state \<phi> t} (rename s1 t) \<and> sem Pr {rename_state \<phi> t} (rename s1 t) = rename_set (sem Pr {\<phi>} s1) t\<close> assms(2) image_iff sem_seq_single by fastforce
    qed
    moreover have "?b \<subseteq> ?a"
    proof (rule subsetI)
      fix x
      let ?x = "rename_state x (rename_inv t)"
      assume "x \<in> ?b"
      then have "?x \<in> sem Pr {\<phi>} (s1 ; s2)"
        using assms(1) member_rename_set_inv by blast
      then obtain y where "y \<in> sem Pr {\<phi>} s1" "?x \<in> sem Pr {y} s2"
        using assms(2) sem_seq_single by auto
      then show "x \<in> ?a"
        using \<open>\<And>\<phi>'. \<phi>' \<in> sem Pr {\<phi>} s1 \<Longrightarrow> ver Pr {rename_state \<phi>' t} (rename s2 t) \<and> sem Pr {rename_state \<phi>' t} (rename s2 t) = rename_set (sem Pr {\<phi>'} s2) t\<close> \<open>ver Pr {rename_state \<phi> t} (rename (s1 ; s2) t)\<close> \<open>ver Pr {rename_state \<phi> t} (rename s1 t) \<and> sem Pr {rename_state \<phi> t} (rename s1 t) = rename_set (sem Pr {\<phi>} s1) t\<close> assms(1) member_rename_set_inv sem_seq_single by auto
    qed
    ultimately show ?thesis
      by blast
  qed
qed

lemma seq_rename_sem_property:
  assumes "rename_sem_property Pr s1 t"
      and "rename_sem_property Pr s2 t"
      and "wf_renaming t"
    shows "rename_sem_property Pr (s1 ; s2) t"
proof -
  have "\<And>\<phi>. wf_stmt Pr s1 \<Longrightarrow> wf_program Pr \<Longrightarrow> ver Pr {\<phi>} s1 \<Longrightarrow> ver Pr {rename_state \<phi> t} (rename s1 t) \<and> sem Pr {rename_state \<phi> t} (rename s1 t) = rename_set (sem Pr {\<phi>} s1) t"
    using assms rename_sem_property_def[of Pr s1] by blast
  moreover have "\<And>\<phi>. wf_stmt Pr s2 \<Longrightarrow> wf_program Pr \<Longrightarrow> ver Pr {\<phi>} s2 \<Longrightarrow> ver Pr {rename_state \<phi> t} (rename s2 t) \<and> sem Pr {rename_state \<phi> t} (rename s2 t) = rename_set (sem Pr {\<phi>} s2) t"
    using assms rename_sem_property_def[of Pr s2] by blast
  ultimately have "\<And>\<phi>. wf_renaming t \<and> ver Pr {\<phi>} (s1 ; s2) \<and> wf_stmt Pr (s1 ; s2) \<and> wf_program Pr \<Longrightarrow>
  ver Pr {rename_state \<phi> t} (rename (s1 ; s2) t) \<and> sem Pr {rename_state \<phi> t} (rename (s1 ; s2) t) = rename_set (sem Pr {\<phi>} (s1 ; s2)) t" 
    using rename_sem_seq(1) rename_sem_seq(2) by auto
  then show ?thesis
    by (simp add: rename_sem_property_def)
qed

lemma wf_program_method_aux:
  "wf_program_aux Pr P \<and> get_method P name = Some m \<Longrightarrow> wf_method Pr m"
proof (induct P)
  case Nil
  then show ?case by simp
next
  case (Cons a P)
  then show ?case
    by (metis get_method.simps(1) option.inject wf_program_aux.simps(2))
qed

lemma wf_method_exists_equiv:
  assumes "get_method Pr m = Some (m, args, ret, P, Q, s)"
  shows "wf_stmt Pr (MethodCall y m x) \<longleftrightarrow> length x = length args
  \<and> length y = length ret \<and> distinct (x @ y)"
  using assms by simp

lemma verif_rename_pred:
  assumes "wf_renaming t"
  shows "(rename_pred P t) a = Some True \<longleftrightarrow> P (rename_state a (rename_inv t)) = Some True"
  by (metis assms renaming_invert_wf rename_pred_same rename_inv_def_state)

lemma smaller_same_one_side:
  assumes "wf_renaming t"
  and "a << b"
  shows "rename_state a t << rename_state b t"
proof -
  obtain c where "Some b = Some a \<oplus> Some c" using assms(2) smaller_def by blast
  then have "Some (rename_state b t) = Some (rename_state a t) \<oplus> Some (rename_state c t)"
    by (simp add: assms(1) rename_state_add)
  then show ?thesis using smaller_def by blast
qed

lemma smaller_same:
  assumes "wf_renaming t"
  shows "a << b \<longleftrightarrow> rename_state a t << rename_state b t"
  by (metis assms rename_inv_def_state renaming_invert_wf smaller_same_one_side)

lemma rename_set_same_order:
  assumes "wf_renaming t"
      and "A >> B"
    shows "rename_set A t >> rename_set B t"
  by (smt assms(1) assms(2) bigger_set_def member_rename_set_inv rename_inv_def_state semantics_algebra.wf_renaming_order semantics_algebra_axioms wf_rename_inv_other)

lemma rename_set_inv:
  assumes "wf_renaming t"
  shows "rename_set (rename_set A t) (rename_inv t) = A" (is "?A = A")
proof -
  have "\<And>x. x \<in> ?A \<longleftrightarrow> x \<in> A"
    by (metis assms member_rename_set_inv semantics_algebra.renaming_invert_wf semantics_algebra_axioms wf_rename_inv_other)
  then show ?thesis
    by blast
qed

lemma rename_set_same_order_equiv:
  assumes "wf_renaming t"
  shows "A >> B \<longleftrightarrow> rename_set A t >> rename_set B t"
  by (metis assms rename_set_inv rename_set_same_order semantics_algebra.renaming_invert_wf semantics_algebra_axioms)

lemma same_wf_rename:
  assumes "wf_assert P"
      and "wf_renaming t"
    shows "wf_assert (rename_pred P t)"
proof -
  let ?P = "rename_pred P t"
  let ?t = "rename_inv t"
  have "\<And>a. (?P a = Some True) \<longleftrightarrow> {a} >> Inh ?P"
  proof -
    fix a
    have "?P a = Some True \<longleftrightarrow> P (rename_state a ?t) = Some True"
      by (simp add: rename_pred_def)
    then have "... \<longleftrightarrow> {rename_state a ?t} >> Inh P"
      using assms(1) wf_assert_def by blast
    then have "... \<longleftrightarrow> rename_set {rename_state a ?t} t >> rename_set (Inh P) t"
      using assms(2) rename_set_same_order_equiv by blast
    then have "... \<longleftrightarrow> {a} >> Inh ?P" 
      by (smt assms(2) image_empty image_insert inh_renamed rename_set.simps wf_rename_inv_other)
    then show "(?P a = Some True) \<longleftrightarrow> {a} >> Inh ?P"
      using \<open>(P (rename_state a (rename_inv t)) = Some True) = ({rename_state a (rename_inv t)} >> Inh P)\<close> \<open>(rename_pred P t a = Some True) = (P (rename_state a (rename_inv t)) = Some True)\<close> \<open>({rename_state a (rename_inv t)} >> Inh P) = (rename_set {rename_state a (rename_inv t)} t >> rename_set (Inh P) t)\<close> by blast
  qed
  moreover have "\<And>a. well_defined_assert ?P a \<longleftrightarrow> (\<forall>i\<in>Inh ?P. a ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> a)" (is "\<And>a. ?a a \<longleftrightarrow> ?b a")
  proof -
    fix a
    let ?aa = "rename_state a (rename_inv t)"
    have "?a a \<longleftrightarrow> ?P a \<noteq> None" 
      by (simp add: well_defined_assert_def)
    then have "... \<longleftrightarrow> P ?aa \<noteq> None" 
      by (simp add: rename_pred_def)
    then have "... \<longleftrightarrow> well_defined_assert P ?aa" 
      by (simp add: well_defined_assert_def)
    then have "... \<longleftrightarrow> (\<forall>i\<in>Inh P. ?aa ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> ?aa)"
      using assms(1) wf_assert_def by auto
    then have "... \<longleftrightarrow> (\<forall>i\<in>Inh ?P. a ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> a)"
    proof -
      have "(\<forall>i\<in>Inh P. ?aa ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> ?aa) \<Longrightarrow> (\<forall>i\<in>Inh ?P. a ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> a)"
      proof -
        assume "\<forall>i\<in>Inh P. ?aa ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> ?aa"
        then have "\<And>i. i \<in> Inh ?P \<and> a ## i \<Longrightarrow> \<sigma> i \<subseteq> \<sigma> a"
        proof -
          fix i assume "i \<in> Inh ?P \<and> a ## i"
          then obtain ii where "ii \<in> Inh P" "i = rename_state ii t" 
            by (metis assms(2) inh_renamed member_rename_set_inv wf_rename_inv_other)
          then have "?aa ## ii"
          proof -
            obtain ai where "Some ai = Some a \<oplus> Some i" 
              using Option.is_none_def \<open>i \<in> Inh (rename_pred P t) \<and> a ## i\<close> defined_def by fastforce
            then have "Some (rename_state ai (rename_inv t)) = Some ?aa \<oplus> Some ii"
              by (simp add: \<open>i = rename_state ii t\<close> assms(2) rename_inv_def_state rename_state_add renaming_invert_wf)
            then show ?thesis 
              by (metis defined_def is_none_code(2))
          qed
          then show "\<sigma> i \<subseteq> \<sigma> a" 
            by (smt \<open>\<forall>i\<in>Inh P. rename_state a (rename_inv t) ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> (rename_state a (rename_inv t))\<close> \<open>i = rename_state ii t\<close> \<open>ii \<in> Inh P\<close> assms(2) image_iff rename_store subsetD subsetI wf_rename_inv_other)
        qed
        then show "\<forall>i\<in>Inh ?P. a ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> a" by blast
      qed
      moreover have "(\<forall>i\<in>Inh ?P. a ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> a) \<Longrightarrow> (\<forall>i\<in>Inh P. ?aa ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> ?aa)"
      proof -
        assume "\<forall>i\<in>Inh ?P. a ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> a"
        then have "\<And>i. i \<in> Inh P \<and> ?aa ## i \<Longrightarrow> \<sigma> i \<subseteq> \<sigma> ?aa"
        proof -
          fix i assume "i \<in> Inh P \<and> ?aa ## i"
          then obtain ii where "ii \<in> Inh ?P" "ii = rename_state i t" 
            by (metis assms(2) inh_renamed rename_inv_def_state semantics_algebra.member_rename_set_inv semantics_algebra_axioms)
          then have "a ## ii"
          proof -
            obtain aai where "Some aai = Some ?aa \<oplus> Some i"  
              by (metis (full_types) \<open>i \<in> Inh P \<and> rename_state a (rename_inv t) ## i\<close> defined_def is_none_simps(1) option.exhaust)
            then have "Some (rename_state aai t) = Some a \<oplus> Some ii" 
              by (simp add: \<open>ii = rename_state i t\<close> assms(2) rename_state_add wf_rename_inv_other)
            then show ?thesis 
              by (metis defined_def is_none_code(2))
          qed
          then have "\<sigma> ii \<subseteq> \<sigma> a" 
            by (simp add: \<open>\<forall>i\<in>Inh (rename_pred P t). a ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> a\<close> \<open>ii \<in> Inh (rename_pred P t)\<close>)
          then show "\<sigma> i \<subseteq> \<sigma> ?aa"
          proof -
            have "a = rename_state ?aa t" 
              by (simp add: assms(2) wf_rename_inv_other)
            then show ?thesis
              by (smt \<open>\<sigma> ii \<subseteq> \<sigma> a\<close> \<open>ii = rename_state i t\<close> assms(2) image_iff rename_inv_def_state rename_store semantics_algebra.renaming_invert_wf semantics_algebra_axioms subsetD subsetI)
          qed
        qed
        then show "\<forall>i\<in>Inh P. ?aa ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> ?aa" by blast
      qed
      then show ?thesis 
        using calculation by linarith
    qed
    then show "?a a \<longleftrightarrow> ?b a" 
      using \<open>(P (rename_state a (rename_inv t)) \<noteq> None) = well_defined_assert P (rename_state a (rename_inv t))\<close> \<open>(rename_pred P t a \<noteq> None) = (P (rename_state a (rename_inv t)) \<noteq> None)\<close> \<open>well_defined_assert (rename_pred P t) a = (rename_pred P t a \<noteq> None)\<close> \<open>well_defined_assert P (rename_state a (rename_inv t)) = (\<forall>i\<in>Inh P. rename_state a (rename_inv t) ## i \<longrightarrow> \<sigma> i \<subseteq> \<sigma> (rename_state a (rename_inv t)))\<close> by blast
  qed
  ultimately show ?thesis
    by (simp add: wf_assert_def)
qed

lemma well_defined_assert_monoin:
  assumes "wf_assert P"
      and "well_defined_assert P a"
      and "a << b"
    shows "well_defined_assert P b"
proof -
  have "\<And>i. i \<in> Inh P \<and> b ## i \<Longrightarrow> \<sigma> i \<subseteq> \<sigma> b"
  proof -
    fix i assume "i \<in> Inh P \<and> b ## i"
    then have "a ## i" 
      by (metis (full_types) Option.is_none_def assms(3) asso3 defined_def orig_comm plus.simps(1) smaller_def)
    then have "\<sigma> i \<subseteq> \<sigma> a"
      using \<open>i \<in> Inh P \<and> b ## i\<close> assms(1) assms(2) wf_assert_def by blast
    then show "\<sigma> i \<subseteq> \<sigma> b"
      using Un_assoc assms(3) semantics_algebra_axioms smaller_def sup.commute sup.orderE sup.orderI store_add by auto
  qed
  then show ?thesis 
    using assms(1) wf_assert_def by auto
qed

lemma wf_stmt_wf_renaming:
  assumes "wf_renaming t"
  shows "wf_stmt Pr s \<longrightarrow> wf_stmt Pr (rename s t)"
proof (induction rule: wf_stmt.induct[of "\<lambda>Pr s. wf_stmt Pr s \<longrightarrow> wf_stmt Pr (rename s t)"])
  case (3 Pr b I s)
  then show ?case
    by (simp add: assms same_wf_rename)
next
  case (4 Pr y m x)
  have "wf_stmt Pr (MethodCall y m x) \<Longrightarrow> wf_stmt Pr (rename (MethodCall y m x) t)"
  proof -
    assume "wf_stmt Pr (MethodCall y m x)"
    obtain args ret P Q s where "get_method Pr m = Some (m, args, ret, P, Q, s)"
      using \<open>wf_stmt Pr (MethodCall y m x)\<close> simple_method_exists by blast
    then have "length x = length args \<and> length y = length ret \<and> distinct (x @ y)"
      using \<open>wf_stmt Pr (MethodCall y m x)\<close> wf_method_exists_equiv by blast

    then have "rename (MethodCall y m x) t = MethodCall (rename_list y t) m (rename_list x t)"
      by simp
    moreover have "length (rename_list y t) = length ret"
      by (simp add: \<open>length x = length args \<and> length y = length ret \<and> distinct (x @ y)\<close> assms rename_list_same_length)
    moreover have "length (rename_list x t) = length args"
      by (simp add: \<open>length x = length args \<and> length y = length ret \<and> distinct (x @ y)\<close> assms rename_list_same_length)
    moreover have "distinct (rename_list x t @ rename_list y t)"
      by (metis \<open>length x = length args \<and> length y = length ret \<and> distinct (x @ y)\<close> assms rename_list_concat rename_list_distinct)
    ultimately show "wf_stmt Pr (rename (MethodCall y m x) t)"
      by (simp add: \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close>)
  qed
  then show ?case by simp
next
  case (5 Pr P)
  then show ?case
    by (simp add: assms same_wf_rename)
next
  case (6 Pr P)
  then show ?case
    by (simp add: assms same_wf_rename)
next
  case (7 Pr other)
  then show ?case
    by (simp add: assms wf_other_renaming)
qed (simp_all)

lemma rename_filter_sigma:
  assumes "wf_renaming t"
  shows "rename_list (filter_sigma x V) t = filter_sigma (rename_state x t) (rename_list V t)"
proof (induction V)
  case Nil
  then show ?case
    by (simp add: filter_sigma_def rename_list_def)
next
  case (Cons a V)
  fix a V assume "rename_list (filter_sigma x V) t = filter_sigma (rename_state x t) (rename_list V t)"
  show "rename_list (filter_sigma x (a # V)) t = filter_sigma (rename_state x t) (rename_list (a # V) t)"
  proof (cases "a \<in> \<sigma> x")
    case True
    then show ?thesis
      using \<open>rename_list (filter_sigma x V) t = filter_sigma (rename_state x t) (rename_list V t)\<close> assms filter_sigma_def rename_list_def rename_store by auto
  next
    case False
    then show ?thesis
      by (smt \<open>rename_list (filter_sigma x V) t = filter_sigma (rename_state x t) (rename_list V t)\<close> assms filter.simps(2) image_iff list.simps(9) rename_store semantics_algebra.filter_sigma_def semantics_algebra.rename_inv_def_elem semantics_algebra.rename_list_def semantics_algebra_axioms)
  qed
qed

lemma rename_all: 
  assumes "wf_renaming t"
  shows "\<And>\<phi>. wf_program Pr \<Longrightarrow> wf_stmt Pr s \<Longrightarrow> ver Pr {\<phi>} s \<Longrightarrow> ver Pr {rename_state \<phi> t} (rename s t) \<and> sem Pr {rename_state \<phi> t} (rename s t) = rename_set (sem Pr {\<phi>} s) t"
proof (induction s)
  case (Inhale P)
  then show ?case 
    using assms rename_sem_inhale(1) rename_sem_inhale(2) wf_stmt.simps(5) by blast
next
  case (Assume x)
  then show ?case
    using assms rename_sem_assume(1) rename_sem_assume(2) by blast
next
  case (Exhale P)
  then show ?case
    using assms rename_sem_exhale(1) rename_sem_exhale(2) by blast
next
  case Skip
  then show ?case
    by (simp add: sem_skip)
next
  case (Seq s1 s2)
  then show ?case
    using assms rename_sem_seq(1) rename_sem_seq(2) by auto
next
  case (If s1 s2)
  then show ?case
    using sem_if_single ver_if by auto
next
  case (Var V)
  then show ?case
    using assms rename_sem_var(1) rename_sem_var(2) by blast
next
  case (Havoc V)
  then show ?case
    using assms rename_sem_havoc(1) rename_sem_havoc(2) by blast
next
  case (MethodCall y m x)
  then show ?case
  proof (cases "get_method Pr m")
    case None
    then show ?thesis using \<open>wf_program Pr\<close> \<open>wf_stmt Pr (MethodCall y m x)\<close>
      by simp
  next
    case (Some a)
    then obtain args ret P Q s where "get_method Pr m = Some (m, args, ret, P, Q, s)"
      using MethodCall.prems(2) simple_method_exists by blast
    let ?P = "rename_pred P (args @ ret, x @ y, [], [])"
    let ?Q = "rename_pred Q (args @ ret, x @ y, [], [])"
    let ?s = "Exhale ?P ; Havoc y ; Inhale ?Q"
    have "rename_sem_property Pr (Havoc y) t"
      using rename_sem_havoc(1) rename_sem_havoc(2) rename_sem_property_def by presburger
    moreover have "rename_sem_property Pr (Inhale ?Q) t"
      using rename_sem_inhale(1) rename_sem_inhale(2) rename_sem_property_def 
      by (meson semantics_algebra.wf_stmt.simps(5) semantics_algebra_axioms)
    ultimately have "rename_sem_property Pr (Havoc y ; Inhale ?Q) t"
      by (simp add: assms seq_rename_sem_property)
    moreover have "rename_sem_property Pr (Exhale ?P) t"
      by (meson rename_sem_exhale(1) rename_sem_exhale(2) semantics_algebra.rename_sem_property_def semantics_algebra_axioms)
    ultimately have "rename_sem_property Pr ?s t"
      by (simp add: \<open>rename_sem_property Pr (Havoc y) t\<close> \<open>rename_sem_property Pr (Inhale ?Q) t\<close> assms seq_rename_sem_property)
    moreover have "ver Pr {\<phi>} ?s" using ver_method_real
      using MethodCall.prems(3) \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> by blast
    moreover have "wf_stmt Pr ?s"
      using MethodCall.prems(1) MethodCall.prems(2) \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> same_wf_rename wf_assert_def wf_program_method_aux by force
    ultimately have "ver Pr {rename_state \<phi> t} (rename ?s t)
\<and> sem Pr {rename_state \<phi> t} (rename ?s t) = rename_set (sem Pr {\<phi>} ?s) t"
      using rename_sem_property_def[of Pr ?s t]
      using MethodCall.prems(1) assms by blast
    moreover have "rename ?s t = Exhale (rename_pred ?P t) ; Havoc (rename_list y t) ; Inhale (rename_pred ?Q t)"
      by auto
    moreover have "wf_renaming (args @ ret, x @ y, [], [])"
      using MethodCall.prems(1) MethodCall.prems(2) \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> wf_program_method_aux by force
    moreover have "set (read_pred P) \<subseteq> set (args @ ret)"
      using MethodCall.prems(1) \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> wf_program_method_aux by fastforce
    then have "rename_pred P (args @ ret, rename_list (x @ y) t, [], []) = rename_pred (rename_pred P (args @ ret, x @ y, [], [])) t"
      by (meson MethodCall.prems(1) \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> assms calculation(3) semantics_algebra.rename_pred_comp_simple semantics_algebra.wf_method.simps semantics_algebra_axioms wf_program.elims(2) wf_program_method_aux)
    moreover have "rename_pred Q (args @ ret, rename_list (x @ y) t, [], []) = rename_pred (rename_pred Q (args @ ret, x @ y, [], [])) t"
      by (metis MethodCall.prems(1) \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> assms calculation(3) rename_pred_comp_simple set_append wf_method.simps wf_program.elims(2) wf_program_method_aux)
    moreover have "rename (MethodCall y m x) t = MethodCall (rename_list y t) m (rename_list x t)"
      by simp
    moreover have "set (rename_list x t) \<union> set (rename_list y t) \<subseteq> \<sigma> (rename_state \<phi> t)"
      using MethodCall.prems(3) \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> assms image_Un rename_list_def rename_store ver_method_real by auto
    ultimately show ?thesis using ver_method_real
      by (smt MethodCall.prems(3) \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> \<open>rename (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], []))) t = Exhale (rename_pred (rename_pred P (args @ ret, x @ y, [], [])) t) ; Havoc (rename_list y t) ; Inhale (rename_pred (rename_pred Q (args @ ret, x @ y, [], [])) t)\<close> \<open>rename_pred P (args @ ret, rename_list (x @ y) t, [], []) = rename_pred (rename_pred P (args @ ret, x @ y, [], [])) t\<close> \<open>rename_pred Q (args @ ret, rename_list (x @ y) t, [], []) = rename_pred (rename_pred Q (args @ ret, x @ y, [], [])) t\<close> \<open>ver Pr {rename_state \<phi> t} (rename (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], []))) t) \<and> sem Pr {rename_state \<phi> t} (rename (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], []))) t) = rename_set (sem Pr {\<phi>} (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], [])))) t\<close> assms rename_list_concat sem_method_real)
  qed
next
  case (While b I s)

  define V where "V = filter_sigma \<phi> (modif s)"

  let ?s = "Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)"
  let ?s' = "Havoc V ; Inhale I ; Assume b ; s ; Exhale I"

  have "rename_sem_property Pr (Assume (lnot b)) t"
    by (meson rename_sem_assume(1) rename_sem_assume(2) semantics_algebra.rename_sem_property_def semantics_algebra_axioms)
  moreover have "rename_sem_property Pr (Inhale I) t"
    using rename_sem_inhale(1) rename_sem_inhale(2) rename_sem_property_def wf_stmt.simps(5) by presburger
  moreover have "rename_sem_property Pr (Havoc V) t"
    using rename_sem_havoc(1) rename_sem_havoc(2) rename_sem_property_def by presburger
  moreover have "rename_sem_property Pr (Exhale I) t"
    using rename_sem_exhale(1) rename_sem_exhale(2) rename_sem_property_def by presburger
  ultimately have "rename_sem_property Pr ?s t"
    by (simp add: \<open>rename_sem_property Pr (Assume (lnot b)) t\<close> \<open>rename_sem_property Pr (Inhale I) t\<close> assms seq_rename_sem_property)
  moreover have "wf_stmt Pr ?s"
    using While.prems(2) wf_assert_def by auto
  moreover have "ver Pr {\<phi>} ?s"
    using V_def While.prems(3) ver_loop by blast
  ultimately have "ver Pr {rename_state \<phi> t} (rename ?s t) \<and>
    sem Pr {rename_state \<phi> t} (rename ?s t) = rename_set (sem Pr {\<phi>} ?s) t" using rename_sem_property_def[of Pr ?s t]
    using While.prems(1) assms by blast
  moreover have "rename_sem_property Pr s t"
    using While.IH rename_sem_property_def by blast
  moreover have "rename_sem_property Pr (Assume b) t"
    using rename_sem_assume(1) rename_sem_assume(2) rename_sem_property_def by presburger
  then have "rename_sem_property Pr ?s' t"
    by (simp add: \<open>rename_sem_property Pr (Exhale I) t\<close> \<open>rename_sem_property Pr (Havoc V) t\<close> \<open>rename_sem_property Pr (Inhale I) t\<close> assms calculation(2) seq_rename_sem_property)
  moreover have "wf_stmt Pr ?s'"
    using While.prems(2) wf_assert_def by auto
  moreover have "ver Pr { |\<phi>| } ?s'"
    using V_def While.prems(3) ver_loop by blast
  ultimately have "ver Pr {rename_state |\<phi>| t} (rename ?s' t) \<and>
    sem Pr {rename_state |\<phi>| t} (rename ?s' t) = rename_set (sem Pr { |\<phi>| } ?s') t" using rename_sem_property_def[of Pr ?s' t]
    using While.prems(1) assms by blast

  let ?b = "rename_pred b t"
  let ?I = "rename_pred I t"
  let ?ss = "rename s t"
  let ?V = "rename_list V t"
  let ?\<phi> = "rename_state \<phi> t"

  have "rename_list V t = filter_sigma ?\<phi> (modif ?ss)" using rename_modif_list V_def
    by (simp add: assms rename_filter_sigma)
  moreover have "rename_pred (lnot b) t = lnot ?b"
    by (simp add: rename_pred_lnot)
  moreover have "rename ?s t = Exhale ?I ; Havoc (rename_list V t) ; Inhale ?I ; Assume (rename_pred (lnot b) t)"
    by simp
  ultimately have "rename ?s t = Exhale ?I ; Havoc (filter_sigma ?\<phi> (modif ?ss)) ; Inhale ?I ; Assume (lnot ?b)"
    by simp

  have "ver Pr {rename_state \<phi> t} (rename (While b I s) t)"
  proof -
    have f1: "rename_state |\<phi>| t = |rename_state \<phi> t|"
      by (simp add: assms wf_core_rename_same)
    have "Havoc (filter_sigma ?\<phi> (modif ?ss)) ; Inhale (rename_pred I t) ; Assume (rename_pred b t) ; rename s t ; Exhale (rename_pred I t) = rename (Havoc V ; Inhale I ; Assume b ; s ; Exhale I) t"
      by (simp add: \<open>rename_list V t = filter_sigma (rename_state \<phi> t) (modif (rename s t))\<close>)
    then show ?thesis
      using \<open>rename (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) t = Exhale (rename_pred I t) ; Havoc (filter_sigma (rename_state \<phi> t) (modif (rename s t))) ; Inhale (rename_pred I t) ; Assume (lnot (rename_pred b t))\<close> \<open>ver Pr {rename_state \<phi> t} (rename (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) t) \<and> sem Pr {rename_state \<phi> t} (rename (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) t) = rename_set (sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b))) t\<close> \<open>ver Pr {rename_state |\<phi>| t} (rename (Havoc V ; Inhale I ; Assume b ; s ; Exhale I) t) \<and> sem Pr {rename_state |\<phi>| t} (rename (Havoc V ; Inhale I ; Assume b ; s ; Exhale I) t) = rename_set (sem Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)) t\<close> f1 ver_loop by force
  qed
  moreover have "sem Pr {rename_state \<phi> t} (rename (While b I s) t) = rename_set (sem Pr {\<phi>} (While b I s)) t"
    using V_def While.prems(3) \<open>rename (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) t = Exhale (rename_pred I t) ; Havoc (filter_sigma (rename_state \<phi> t) (modif (rename s t))) ; Inhale (rename_pred I t) ; Assume (lnot (rename_pred b t))\<close> \<open>ver Pr {rename_state \<phi> t} (rename (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) t) \<and> sem Pr {rename_state \<phi> t} (rename (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) t) = rename_set (sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b))) t\<close> calculation sem_loop by auto
  ultimately show ?case by blast
next
  case (Other other)
  then have "ver Pr {rename_state \<phi> t} (rename (Other other) t)"
    using assms ver_def ver_rename_other by auto
  moreover have "sem Pr {rename_state \<phi> t} (rename (Other other) t) = rename_set (sem Pr {\<phi>} (Other other)) t"
  proof -
    have "\<And>x. x \<in> sem Pr {rename_state \<phi> t} (rename (Other other) t) \<longleftrightarrow> x \<in> rename_set (sem Pr {\<phi>} (Other other)) t"
    proof -
      fix x
      have "x \<in> sem Pr {rename_state \<phi> t} (rename (Other other) t) \<longleftrightarrow>
            x \<in> get_S (semantics_other Pr (rename_state \<phi> t) (rename_other other t))" by simp
      moreover have "... \<longleftrightarrow> rename_state x (rename_inv t) \<in> get_S (semantics_other Pr \<phi> other)" (is "?a \<longleftrightarrow> ?b")
      proof -
        have "?a \<Longrightarrow> ?b"
          using assms semantics_rename_other by auto
        moreover have "?b \<Longrightarrow> ?a"
        proof -
          assume "?b"
          then have "rename_state (rename_state x (rename_inv t)) t \<in> get_S (semantics_other Pr (rename_state \<phi> t) (rename_other other t))"
            using semantics_rename_other assms rename_inv_def_other rename_inv_def_state renaming_invert_wf
            by metis
          then show "?a"
            by (metis assms rename_inv_def_state semantics_algebra.renaming_invert_wf semantics_algebra_axioms)
        qed
        ultimately show ?thesis by blast
      qed
      moreover have "... \<longleftrightarrow> x \<in> rename_set (get_S (semantics_other Pr \<phi> other)) t"
        using member_rename_set_inv[of t x "get_S (semantics_other Pr \<phi> other)"] \<open>wf_renaming t\<close>
        by simp
      ultimately show "x \<in> sem Pr {rename_state \<phi> t} (rename (Other other) t) \<longleftrightarrow> x \<in> rename_set (sem Pr {\<phi>} (Other other)) t" by simp
    qed
    then show ?thesis by blast
  qed
  ultimately show ?case by simp
qed

lemma rename_ver:
  assumes "wf_renaming t"
      and "wf_program Pr"
      and "wf_stmt Pr s"
  shows "ver Pr {\<phi>} s \<longleftrightarrow> ver Pr {rename_state \<phi> t} (rename s t)" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b" using rename_all[of t Pr s \<phi>] assms by simp
  moreover have "wf_stmt Pr (rename s t)"
    by (simp add: assms(1) assms(3) wf_stmt_wf_renaming)
  then have "?b \<Longrightarrow> ?a" using rename_all[of "rename_inv t" Pr "rename s t" "rename_state \<phi> t"] assms
    using rename_inv_def_state renaming_invert renaming_invert_wf by auto
  then show ?thesis
    using calculation by blast
qed

lemma rename_sem:
  assumes "wf_renaming t"
      and "wf_program Pr"
      and "wf_stmt Pr s"
      and "ver Pr {\<phi>} s"
  shows "sem Pr {rename_state \<phi> t} (rename s t) = rename_set (sem Pr {\<phi>} s) t"
  using assms rename_all[of t Pr s \<phi>] by simp

lemma rename_ver_set:
  assumes "ver Pr A s"
  and "wf_renaming t"
  and "wf_program Pr"
  and "wf_stmt Pr s"
  shows "ver Pr (rename_set A t) (rename s t)"
  using assms image_iff rename_set.simps rename_ver semantics_algebra_axioms v_singleton
  by smt

lemma method_verif_rename:
  assumes "ver Pr {u} (Var (args @ ret) ; Inhale P ; s ; Exhale Q)"
      and "wf_renaming (args @ ret, x @ y, l, do)"
      and "wf_program Pr"
      and "wf_stmt Pr (Var (args @ ret) ; Inhale P ; s ; Exhale Q)"
  shows "ver Pr {u} (Var (x @ y) ; Inhale (rename_pred P (args @ ret, x @ y, l, do)) ;
      rename s (args @ ret, x @ y, l, do) ; Exhale (rename_pred Q (args @ ret, x @ y, l, do)))"
proof -
  let ?s = "Var (args @ ret) ; Inhale P ; s ; Exhale Q"
  let ?s' = "Var (x @ y) ; Inhale (rename_pred P (args @ ret, x @ y, l, do)) ;
      rename s (args @ ret, x @ y, l, do) ; Exhale (rename_pred Q (args @ ret, x @ y, l, do))"
  let ?t = "(args @ ret, x @ y, l, do)"
  have "Inhale (rename_pred P ?t) = rename (Inhale P) ?t" by simp
  then have "rename ?s ?t = ?s'"
    using assms(2) rename_list_same by auto
  then show ?thesis
    by (metis assms rename_set_empty rename_ver_set)
qed

lemma sem_method:
  assumes "ver Pr {\<phi>} (MethodCall y m x)"
      and "wf_stmt Pr (MethodCall y m x)"
  shows "\<exists> args ret P Q s. get_method Pr m = Some (m, args, ret, P, Q, s) \<and>
        sem Pr {\<phi>} (MethodCall y m x) = sem Pr {\<phi>} (Exhale (rename_pred P (args @ ret, x @ y, [], [])); Havoc y ;
                      Inhale (rename_pred Q (args @ ret, x @ y, [], [])))"
  by (meson assms(1) assms(2) sem_method_real simple_method_exists)

lemma wf_program_method:
  assumes "wf_program Pr"
      and "get_method Pr name = Some m"
    shows "wf_method Pr m"
  using assms(1) assms(2) wf_program_method_aux by auto

lemma ver_method:
  assumes "ver Pr {\<phi>} (MethodCall y m x)"
      and "wf_stmt Pr (MethodCall y m x)"
      and "wf_program Pr"
  shows "\<exists>args ret P Q s.
          wf_method Pr (m, args, ret, P, Q, s) \<and>
          ver Pr {\<phi>} (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], []))) \<and>
          (set x \<union> set y) \<subseteq> \<sigma> \<phi> \<and>
          length args = length x \<and> length ret = length y"
proof -
  obtain args ret P Q s where asm: "get_method Pr m = Some (m, args, ret, P, Q, s)"
    using assms sem_method by blast
  then have "wf_method Pr (m, args, ret, P, Q, s)"
    using assms(3) wf_program_method by blast
  moreover have "ver Pr {\<phi>} (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], [])))"
    using \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> assms(1) ver_method_real by blast
  moreover have "(set x \<union> set y) \<subseteq> \<sigma> \<phi>"
    using \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> assms(1) ver_method_real by blast
  moreover have "length args = length x \<and> length ret = length y"
  proof -
    have "(let r = get_method Pr m in
  r \<noteq> None \<and> (let (_, args, ret, _, _, _) = the r in length x = length args
  \<and> length y = length ret \<and> distinct (x @ y)))"
      using assms(2) wf_stmt.simps(4) by blast
    then show ?thesis using asm by simp
  qed
  ultimately show ?thesis by blast
qed

lemma modif_property_other:
  "wf_program Pr \<and> wf_other Pr other \<and> ver Pr {a} (Other other) \<and> c \<in> sem Pr {a} (Other other) \<longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif (Other other))"
  using modif_other_sem[of Pr other c a] by simp

definition modif_property :: "('a, 'b, 'c) program \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "modif_property Pr s \<longleftrightarrow> (\<forall>a c. wf_program Pr \<and> wf_stmt Pr s \<and> ver Pr {a} s \<and> c \<in> sem Pr {a} s \<longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s))"

lemma modif_property_inhale:
  "modif_property Pr (Inhale P)"
  using modif_property_def store_same_pred_supp_inhale by auto

lemma modif_property_exhale:
  "modif_property Pr (Exhale P)"
  by (metis Un_upper1 modif_property_def set_eq_subset store_same_pred_supp_exhale wf_stmt.simps(6))

lemma modif_property_havoc:
  "modif_property Pr (Havoc y)"
proof -
  let ?s = "Havoc y"
  have "\<And>a c. wf_program Pr \<and> wf_stmt Pr ?s \<and> ver Pr {a} ?s \<and> c \<in> sem Pr {a} ?s \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif ?s)"
    by (metis Diff_partition commutative h_comp_store h_store modif.simps(9) sem_havoc sep_algebra.set_add_elem sep_algebra_axioms singletonD store_add sup.idem sup.order_iff ver_havoc)
  then show ?thesis
    by (simp add: modif_property_def)
qed

lemma store_modif_sem_seq:
  assumes "s = s1 ; s2"
      and "\<And>a c. wf_program Pr \<and> wf_stmt Pr s1 \<and> ver Pr {a} s1 \<and> c \<in> sem Pr {a} s1 \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s1)"
      and "\<And>a c. wf_program Pr \<and> wf_stmt Pr s2 \<and> ver Pr {a} s2 \<and> c \<in> sem Pr {a} s2 \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s2)"
      and "wf_program Pr \<and> wf_stmt Pr s \<and> ver Pr {a} s \<and> c \<in> sem Pr {a} s"
    shows "\<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s)"
proof -
  obtain b where "b \<in> sem Pr {a} s1" "c \<in> sem Pr {b} s2"
    using assms(1) assms(4) sem_seq_single by auto
  then obtain "\<sigma> a \<subseteq> \<sigma> b" "\<sigma> b \<subseteq> \<sigma> a \<union> set (modif s1)"
    using assms(1) assms(2) assms(4) ver_seq by auto
  moreover obtain "\<sigma> b \<subseteq> \<sigma> c" "\<sigma> c \<subseteq> \<sigma> b \<union> set (modif s2)"
    by (metis \<open>b \<in> sem Pr {a} s1\<close> \<open>c \<in> sem Pr {b} s2\<close> assms(1) assms(3) assms(4) v_singleton ver_seq wf_stmt.simps(1))
  ultimately have "\<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s1) \<union> set (modif s2)"
    by blast
  then show ?thesis
    by (simp add: Un_assoc assms(1))
qed

lemma modif_property_seq:
  assumes "modif_property Pr s1"
      and "modif_property Pr s2"
    shows "modif_property Pr (s1 ; s2)"
proof -
  obtain "\<And>a c. wf_program Pr \<and> wf_stmt Pr s1 \<and> ver Pr {a} s1 \<and> c \<in> sem Pr {a} s1 \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s1)"
      "\<And>a c. wf_program Pr \<and> wf_stmt Pr s2 \<and> ver Pr {a} s2 \<and> c \<in> sem Pr {a} s2 \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s2)"
    using assms(1) assms(2) modif_property_def by blast
  then have "\<And>a c. wf_program Pr \<and> wf_stmt Pr (s1 ; s2) \<and> ver Pr {a} (s1 ; s2) \<and> c \<in> sem Pr {a} (s1 ; s2) \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif (s1 ; s2))"
    using store_modif_sem_seq by blast
  then show ?thesis
    by (simp add: modif_property_def)
qed

lemma modif_property_assume:
  "modif_property Pr (Assume b)"
  by (smt Diff_cancel Diff_eq_empty_iff Un_upper1 empty_iff get_S.simps(1) modif_property_def semantics_algebra.semantics.simps(2) semantics_algebra.ver_def semantics_algebra_axioms singletonD singletonI singleton_sem)

lemma wf_wf_renaming:
  assumes "wf_program Pr"
      and "wf_stmt Pr (MethodCall y m x)"
      and "get_method Pr m = Some (m, args, ret, P, Q, s)"
    shows "wf_renaming (args @ ret, x @ y, l, do)"
      and "wf_renaming (args @ ret, x @ y, l, do)"
proof -
  have "distinct (x @ y)" using assms by simp
  moreover have "distinct (args @ ret)" using assms
    using wf_method.simps wf_program_method by blast
  moreover obtain "length x = length args" "length y = length ret" using assms by simp
  ultimately show "wf_renaming (args @ ret, x @ y, l, do)" "wf_renaming (args @ ret, x @ y, l, do)" by simp_all
qed

lemma filter_sigma_included:
  "set (filter_sigma a V) \<subseteq> set V"
  apply (induction V)
  apply (simp add: filter_sigma_def)
  using filter_sigma_def by auto

lemma store_modif_sem: "wf_program Pr \<and> wf_stmt Pr s \<and> ver Pr {a} s \<and> c \<in> sem Pr {a} s \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s)"
proof (induct arbitrary: a c rule: modif.induct)
  case (1 s1 s2)
  obtain b where "b \<in> sem Pr {a} s1" "c \<in> sem Pr {b} s2"
    using "1.prems" sem_seq by force
  then obtain "\<sigma> a \<subseteq> \<sigma> b" "\<sigma> b \<subseteq> \<sigma> a \<union> set (modif s1)"
    using "1.hyps"(1) "1.prems" ver_seq_single
    using wf_stmt.simps(1) by blast
  moreover obtain "\<sigma> b \<subseteq> \<sigma> c" "\<sigma> c \<subseteq> \<sigma> b \<union> set (modif s2)"
    by (meson "1.hyps"(2) "1.prems" \<open>b \<in> sem Pr {a} s1\<close> \<open>c \<in> sem Pr {b} s2\<close> v_singleton ver_seq wf_stmt.simps(1))
  ultimately have "\<sigma> a \<subseteq> \<sigma> c \<and> \<sigma> c \<subseteq> \<sigma> a \<union> set (modif s1) \<union> set (modif s2)"
    by blast
  then show ?case
    by (simp add: inf_sup_aci(6))
next
  case (2 s1 s2)
  then show ?case
    by (smt Un_assoc Un_iff inf_sup_aci(5) modif.simps(2) sem_if set_append sup.absorb_iff2 ver_if wf_stmt.simps(2))
next
  case (3 y m x)
  obtain args ret P Q s where "get_method Pr m = Some (m, args, ret, P, Q, s)"
    using "3.prems" simple_method_exists by blast
  let ?P = "rename_pred P (args @ ret, x @ y, [], [])"
  let ?Q = "rename_pred Q (args @ ret, x @ y, [], [])"
  let ?s = "Exhale ?P ; Havoc y ; Inhale ?Q"
  have "wf_stmt Pr ?s"
  proof -
    have "wf_renaming (args @ ret, x @ y, [], [])" using wf_wf_renaming(1)[of Pr y m x args ret P Q s]
      using "3.prems" \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> by blast
    moreover have "wf_assert P"
      using "3.prems" \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> wf_program_method by auto
    moreover have "wf_renaming (args @ ret, x @ y, [], [])" using wf_wf_renaming(2)[of Pr y m x args ret P Q s]
      using "3.prems" \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> by blast
    moreover have "wf_assert Q"
      using "3.prems" \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> wf_program_method by auto
    ultimately show ?thesis
      by (simp add: same_wf_rename)
  qed
  moreover have "ver Pr {a} ?s \<and> c \<in> sem Pr {a} ?s"
    by (metis "3.prems" \<open>get_method Pr m = Some (m, args, ret, P, Q, s)\<close> sem_method_real semantics_algebra.ver_method_real semantics_algebra_axioms)
  ultimately show ?case
  proof -
    have "modif_property Pr ?s"
      by (simp add: modif_property_exhale modif_property_havoc modif_property_inhale modif_property_seq)
    then show ?thesis
      by (metis "3.prems" \<open>ver Pr {a} (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], []))) \<and> c \<in> sem Pr {a} (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], [])))\<close> \<open>wf_stmt Pr (Exhale (rename_pred P (args @ ret, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ ret, x @ y, [], [])))\<close> modif.simps(1) modif.simps(3) modif.simps(6) modif.simps(7) modif.simps(9) modif_property_def self_append_conv self_append_conv2)
  qed
next
  case (4 b I s)
  let ?s = "Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I ; Assume (lnot b)"
  have "modif_property Pr ?s"
    by (simp add: modif_property_assume modif_property_exhale modif_property_havoc modif_property_inhale modif_property_seq)
  moreover have "ver Pr {a} ?s \<and> c \<in> sem Pr {a} ?s"
    using "4.prems" sem_loop ver_loop by blast
  moreover have "wf_stmt Pr ?s"
    using "4.prems" wf_assert_def by auto
  ultimately have "\<sigma> a \<subseteq> \<sigma> c"
    using "4.prems" modif_property_def by blast
  moreover have "\<sigma> c \<subseteq> \<sigma> a \<union> set (modif ?s)"
    using "4.prems" \<open>modif_property Pr (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I ; Assume (lnot b))\<close> \<open>ver Pr {a} (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I ; Assume (lnot b)) \<and> c \<in> sem Pr {a} (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I ; Assume (lnot b))\<close> \<open>wf_stmt Pr (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I ; Assume (lnot b))\<close> modif_property_def by blast
  moreover have "set (filter_sigma a (modif s)) \<subseteq> set (modif s)"
    using filter_sigma_included by blast
  ultimately show ?case
    by auto
next
  case (5 b)
  then show ?case
    using modif_property_assume modif_property_def by blast
next
  case (6 P)
  then show ?case 
    using store_same_pred_supp_inhale by force
next
  case (7 P)
  then show ?case
    using store_same_pred_supp_exhale by auto
next
  case (8 l)
  then show ?case
    by (metis Un_upper1 h_store modif.simps(8) sem_var sep_algebra.set_add_elem sep_algebra_axioms singletonD store_add sup.idem)
next
  case (9 l)
  then show ?case
    by (metis Un_Diff_cancel2 Un_upper1 h_comp_store h_store modif.simps(9) sem_havoc sep_algebra.set_add_elem sep_algebra_axioms singletonD store_add sup.idem)
next
  case 10
  then show ?case
    by auto
next
  case (11 s)
  then show ?case
    using modif_property_other wf_stmt.simps(7) by blast
qed

lemma ver_method_set_ret:
  assumes "ver Pr {\<phi>} (MethodCall y m x)"
      and "get_method Pr m = Some (m, args, ret, P, Q, s)"
      and "a \<in> sem Pr {u} (Var (args @ ret) ; Inhale P ; s ; Exhale Q)"
      and "ver Pr {u} (Var (args @ ret) ; Inhale P ; s ; Exhale Q)"
      and "wf_program Pr"
    shows "set ret \<subseteq> \<sigma> a"
proof -
  have "set (modif (Var (args @ ret))) \<subseteq> set (modif (Var (args @ ret) ; Inhale P ; s ; Exhale Q))"
    by auto
  moreover have "set (modif (Var (args @ ret))) = set (args @ ret)" by auto
  moreover have "a \<in> sem Pr (sem Pr {u} (Var (args @ ret))) (Inhale P ; s ; Exhale Q)"
    using sem_seq[of Pr "{u}" "Var (args @ ret)"] assms(3) assms(4)
    by (smt sem_seq ver_seq)
  then obtain b where "b \<in> sem Pr {u} (Var (args @ ret))" "a \<in> sem Pr {b} (Inhale P ; s ; Exhale Q)"
    using elem_sem by blast
  then have "set ret \<subseteq> \<sigma> b"
    by (smt Int_empty_right Un_absorb add_sets_neutral h_store inf_sup_aci(7) sem_var set_append simple_set_add_comm store_empty subset_Un_eq ver_var)
  moreover have "\<sigma> b \<subseteq> \<sigma> a"
  proof -
    have "wf_stmt Pr (Inhale P ; s ; Exhale Q)"
      using assms(2) assms(5) wf_assert_def wf_program_method 
      using semantics_algebra.wf_stmt.simps(5) by fastforce
    then show ?thesis using store_modif_sem[of Pr "Inhale P ; s ; Exhale Q" b a]
        \<open>a \<in> sem Pr {b} (Inhale P ; s ; Exhale Q)\<close> \<open>b \<in> sem Pr {u} (Var (args @ ret))\<close> assms(4) sem_seq v_singleton ver_seq
      by (smt assms(5))
  qed
  ultimately show ?thesis
    by blast
qed

lemma h_comp_only_pure: "C \<phi> = C (h_comp \<phi> l)"
proof -
  have f1: "pure |\<phi>|"
    by (metis (no_types) sep_algebra.core_properties(1) sep_algebra_axioms)
  have "s_C \<phi> = s_C (h_comp \<phi> l) \<oplus> s_C |\<phi>|"
    by (metis h_comp_sum s_core_def sep_algebra.c_add sep_algebra_axioms)
  then show ?thesis
    using f1 by (simp add: orig_neutral pure_c s_C_def)
qed

lemma h_comp_smaller: "h_comp \<phi> x << \<phi>"
  using h_comp_sum s_core_def smaller_def by auto

lemma var_sem_empty:
  "sem Pr {u} (Var x) = h x"
  by (metis Int_empty_right add_sets_neutral sem_var simple_set_add_comm store_empty ver_var)

lemma havoc_concat:
  "h (a @ b) = h a \<oplus>\<oplus> h b"
  by (simp add: h_lin)

lemma havoc_store_bigger:
  assumes "set x \<subseteq> \<sigma> \<phi>"
  shows "{\<phi>} >> {\<phi>} \<oplus>\<oplus> h x"
proof -
  have "\<exists>hx \<in> h x. Some \<phi> = Some \<phi> \<oplus> Some hx" by (meson assms h_bigger h_pure pure_smaller_ok
        commutative_monoid_axioms bigger_set_def sep_algebra_axioms singletonI)
  then show ?thesis by (metis bigger_set_def set_add_elem_reci singletonD smaller_refl)
qed

lemma supported_intui_exhale:
  assumes "wf_assert P"
    shows "ver Pr A (Exhale P) \<longleftrightarrow> A >> Inh P"
proof -
  have "\<And>a. ver Pr {a} (Exhale P) \<longleftrightarrow> (\<exists>\<phi> \<in> Inh P. \<phi> << a)"
  proof -
    fix a
    have "ver Pr {a} (Exhale P) \<Longrightarrow> (\<exists>\<phi> \<in> Inh P. \<phi> << a)"
      using assms bigger_set_def exhale_verif wf_assert_def by auto
    moreover have "(\<exists>\<phi> \<in> Inh P. \<phi> << a) \<Longrightarrow> ver Pr {a} (Exhale P)"
    proof -
      assume "\<exists>\<phi> \<in> Inh P. \<phi> << a"
      then obtain \<phi> where "\<phi> \<in> Inh P" and "\<phi> << a" by blast
      then show "ver Pr {a} (Exhale P)"
        using assms bigger_set_def singletonD ver_exhale wf_assert_def by auto
    qed
    ultimately show "ver Pr {a} (Exhale P) \<longleftrightarrow> (\<exists>\<phi> \<in> Inh P. \<phi> << a)" by blast
  qed
  then show ?thesis by (metis (no_types, lifting) bigger_set_def v_singleton)
qed

lemma int_squared_inhale:
  assumes "wf_assert P"
      and "Some \<phi>' = Some \<phi> \<oplus> Some r"
      and "ver Pr {\<phi>} (Inhale P)"
    shows "sem Pr {\<phi>'} (Inhale P) = (sem Pr {\<phi>} (Inhale P)) \<oplus>\<oplus> {r}"
proof -
  have "ver Pr {\<phi>'} (Inhale P)"
    by (meson assms(1) assms(2) assms(3) semantics_algebra.ver_inhale_single semantics_algebra_axioms smaller_def well_defined_assert_monoin)
  then show ?thesis
  proof -
    have f1: "sem Pr {\<phi>'} (Inhale P) = {\<phi>'} \<oplus>\<oplus> Inh P"
      by (meson \<open>ver Pr {\<phi>'} (Inhale P)\<close> semantics_algebra.sem_inhale semantics_algebra.ver_inhale semantics_algebra_axioms)
    have "sem Pr {\<phi>} (Inhale P) = {\<phi>} \<oplus>\<oplus> Inh P"
      by (meson assms(3) semantics_algebra.sem_inhale semantics_algebra.ver_inhale semantics_algebra_axioms)
    then show ?thesis
      using f1 assms(2) set_add_asso simple_set_add simple_set_add_comm by auto
  qed
qed

lemma wf_assert_monoIn:
  assumes "wf_assert P"
  shows "ssafeMono Pr A (Inhale P)"
    and "ssafeMono Pr A (Exhale P)"
  using assms ssafeMono_singleton ver_inhale_single wf_assert_def apply auto[1]
  apply (meson assms subset_iff well_defined_assert_monoin)
proof (rule ssafeMonoI)
  fix x y
  assume asm: "x << y \<and> (\<exists>a\<in>A. y << a) \<and> ver Pr {x} (Exhale P)"
  then show "ver Pr {y} (Exhale P)"
    by (metis assms bigger_set_def singleton_iff smaller_trans supported_intui_exhale)
qed

lemma int_squared_inhale_for_sets:
  assumes "wf_assert P"
      and "ver Pr A (Inhale P)"
    shows "sem Pr (A \<oplus>\<oplus> {r}) (Inhale P) = (sem Pr A (Inhale P)) \<oplus>\<oplus> {r}"
proof -
  have "ver Pr (A \<oplus>\<oplus> {r}) (Inhale P)"
    by (metis assms(1) assms(2) can_read_false mem_Collect_eq rel_bigger_add_set smaller_refl ssafeMono_def wf_assert_monoIn(1))
  then show ?thesis
    using assms(2) sem_inhale set_add_asso simple_set_add_comm ver_inhale by auto
qed

lemma smono_singleton:
  "smono Pr A s \<longleftrightarrow> (\<forall>a \<in> A. smono Pr {a} s)" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b"
  proof -
    assume "?a"
    then have "\<And>a B. (\<exists>x \<in> A. a << x) \<and> {a} >> B \<and> ver Pr B s \<Longrightarrow> ver Pr {a} s \<and> sem Pr {a} s >> sem Pr B s"
    proof -
      fix a B assume "(\<exists>x \<in> A. a << x) \<and> {a} >> B \<and> ver Pr B s"
      obtain b where "b \<in> B" "b << a"
        using \<open>(\<exists>x\<in>A. a << x) \<and> {a} >> B \<and> ver Pr B s\<close> bigger_set_def by auto
      then have "ver Pr {a} s"
        by (meson \<open>(\<exists>x\<in>A. a << x) \<and> {a} >> B \<and> ver Pr B s\<close> \<open>smono Pr A s\<close> semantics_algebra.smono_def semantics_algebra.v_singleton semantics_algebra_axioms ssafeMono_singleton)
      then show "ver Pr {a} s \<and> sem Pr {a} s >> sem Pr B s"
        by (metis \<open>(\<exists>x\<in>A. a << x) \<and> {a} >> B \<and> ver Pr B s\<close> \<open>smono Pr A s\<close> singletonD smonoOut_def smono_def)
    qed
    then show "?b" 
      using \<open>smono Pr A s\<close> empty_subsetI singletonD smonoOut_def smono_def ssafeMono_singleton subset_singletonD
      by smt
  qed
  moreover have "?b \<Longrightarrow> ?a"
    using local.mono_def mono_smono by auto
  ultimately show ?thesis by blast
qed

lemma smono_bigger_ok:
  assumes "smono Pr B s"
      and "A \<subseteq> B"
    shows "smono Pr A s"
  by (meson assms(1) assms(2) smono_singleton subsetD)

lemma monoI:
  "(\<And>a b. b << a \<and> ver Pr {b} s \<and> (\<exists>x \<in> A. a << x) \<Longrightarrow> ver Pr {a} s \<and> sem Pr {a} s >> sem Pr {b} s)
  \<Longrightarrow> mono Pr A s" 
  by (meson mono_smono smonoOutI smono_def ssafeMonoI)

lemma mono_if:
  assumes "mono Pr A s1"
      and "mono Pr A s2"
    shows "mono Pr A (If s1 s2)"
proof (rule monoI)
  let ?s = "If s1 s2"
  fix a b assume "b << a \<and> ver Pr {b} ?s \<and> (\<exists>x \<in> A. a << x)"
  then have "ver Pr {a} s1 \<and> sem Pr {a} s1 >> sem Pr {b} s1"
    by (meson assms(1) mono_smono semantics_algebra.ver_if semantics_algebra_axioms smonoOut_singleton smono_def ssafeMono_singleton)
  moreover have "ver Pr {a} s2 \<and> sem Pr {a} s2 >> sem Pr {b} s2"
    by (metis \<open>b << a \<and> ver Pr {b} (stmt.If s1 s2) \<and> (\<exists>x \<in> A. a << x)\<close> assms(2) mono_smono semantics_algebra.smono_def semantics_algebra.ssafeMono_singleton semantics_algebra_axioms smonoOut_singleton ver_if)
  ultimately show "ver Pr {a} (stmt.If s1 s2) \<and> sem Pr {a} (stmt.If s1 s2) >> sem Pr {b} (stmt.If s1 s2)"
    using \<open>b << a \<and> ver Pr {b} (stmt.If s1 s2) \<and> (\<exists>x \<in> A. a << x)\<close> bigger_set_union sem_if_single ver_if by auto
qed

fun framing :: "('a, 'b, 'c) program \<Rightarrow> 'a set \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "framing Pr A st = (smono Pr A st \<and>
  (\<forall>\<phi> r. (\<exists>s a. Some s = Some \<phi> \<oplus> Some r \<and> s << a \<and> a \<in> A) \<and> ver Pr {\<phi>} st \<and> list.set (modif st) \<inter> \<sigma> r = {} \<longrightarrow> (sem Pr ({\<phi>} \<oplus>\<oplus> {r}) st >> (sem Pr {\<phi>} st \<oplus>\<oplus> {r}))))"

lemma simple_rename_set_inv:
  assumes "wf_renaming t"
  shows "rename_set (rename_set A t) (rename_inv t) = A"
proof -
  let ?t = "rename_inv t"
  have "rename_set (rename_set A t) ?t = (\<lambda>x. rename_state x ?t) ` (rename_set A t)"
    by simp
  then have "... = (\<lambda>x. rename_state x ?t) ` ((\<lambda>y. rename_state y t) ` A)"
    by simp
  then have "... = (\<lambda>y. rename_state (rename_state y t) ?t) ` A" by blast
  moreover have "(\<lambda>y. rename_state (rename_state y t) ?t) = (\<lambda>y. y)"
  proof (rule ext)
    fix y
    show "rename_state (rename_state y t) ?t = y"
      by (simp add: assms rename_inv_def_state)
  qed
  ultimately have "rename_set (rename_set A t) ?t = (\<lambda>y. y) ` A"
    using \<open>(\<lambda>x. rename_state x (rename_inv t)) ` rename_set A t = (\<lambda>x. rename_state x (rename_inv t)) ` (\<lambda>y. rename_state y t) ` A\<close> \<open>rename_set (rename_set A t) (rename_inv t) = (\<lambda>x. rename_state x (rename_inv t)) ` rename_set A t\<close> by presburger
  then show ?thesis
    by blast
qed

lemma simple_state_in_set:
  assumes "wf_renaming t"
  shows "rename_state a t \<in> rename_set A t \<longleftrightarrow> a \<in> A" (is "?a \<longleftrightarrow> ?b")
  by (smt Set.set_insert assms image_insert insert_iff rename_set.simps simple_rename_set_inv)

lemma simple_renaming_from_set:
  assumes "x \<in> rename_set A t"
  shows "\<exists>a \<in> A. x = rename_state a t"
  using assms by auto

lemma rename_set_sum:
  assumes "wf_renaming t"
  shows "rename_set (A \<oplus>\<oplus> B) t = rename_set A t \<oplus>\<oplus> rename_set B t"
proof -
  let ?a = "rename_set (A \<oplus>\<oplus> B) t"
  let ?b = "rename_set A t \<oplus>\<oplus> rename_set B t"
  have "?a \<subseteq> ?b"
  proof (rule subsetI)
    fix x assume "x \<in> ?a"
    then obtain xx where "xx \<in> A \<oplus>\<oplus> B" "x = rename_state xx t" by auto
    then obtain a b where "Some xx = Some a \<oplus> Some b" "a \<in> A" "b \<in> B"
      using set_add_elem by blast
    then have "Some x = Some (rename_state a t) \<oplus> Some (rename_state b t)"
      using \<open>x = rename_state xx t\<close> assms rename_state_add by blast
    then show "x \<in> ?b"
      using \<open>a \<in> A\<close> \<open>b \<in> B\<close> elem_add_set by auto
  qed
  moreover have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix x assume "x \<in> ?b"
    then obtain aa bb where "aa \<in> rename_set A t" "bb \<in> rename_set B t" "Some x = Some aa \<oplus> Some bb"
      using set_add_elem by blast
    then obtain a b where "aa = rename_state a t" "bb = rename_state b t" "a \<in> A" "b \<in> B"
      by auto
    let ?t = "rename_inv t"
    let ?x = "rename_state x ?t"
    have "Some ?x = Some a \<oplus> Some b"
      by (simp add: \<open>Some x = Some aa \<oplus> Some bb\<close> \<open>aa = rename_state a t\<close> \<open>bb = rename_state b t\<close> assms rename_state_add rename_inv_def_state renaming_invert_wf)
    moreover have "x = rename_state ?x t"
      by (metis assms rename_inv_def_state renaming_invert_wf)
    ultimately show "x \<in> ?a"
      using \<open>a \<in> A\<close> \<open>b \<in> B\<close> set_add_elem_reci by auto
  qed
  ultimately show ?thesis by blast
qed

lemma rename_set_smaller:
  assumes "wf_renaming t"
  shows "A >> B \<longleftrightarrow> rename_set A t >> rename_set B t" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b"
    by (smt assms bigger_set_def rename_inv_def_state simple_rename_set_inv simple_renaming_from_set smaller_same)
  moreover have "?b \<Longrightarrow> ?a"
    by (smt assms bigger_set_def rename_inv_def_state simple_rename_set_inv simple_renaming_from_set smaller_same)
  ultimately show ?thesis by blast
qed

lemma mono_renamed:
  assumes "smono Pr D s"
      and "wf_renaming t"
      and "wf_program Pr"
      and "wf_stmt Pr s"
    shows "smono Pr (rename_set D t) (rename s t)"
proof -
  let ?s = "rename s t"
  let ?t = "rename_inv t"
  let ?D = "rename_set D t"
  have "\<And>a b. a << b \<and> ver Pr {a} ?s \<and> (\<exists>d \<in> ?D. b << d) \<Longrightarrow> ver Pr {b} ?s \<and> sem Pr {b} ?s >> sem Pr {a} ?s"
  proof -
    fix a b assume asm: "a << b \<and> ver Pr {a} ?s \<and> (\<exists>d \<in> ?D. b << d)"
    let ?a = "rename_state a ?t"
    let ?b = "rename_state b ?t"
    have "?a << ?b \<and> ver Pr {?a} s \<and> (\<exists>d \<in> D. ?b << d)"
      by (metis (full_types) asm assms(2) assms(3) assms(4) member_rename_set_inv semantics_algebra.rename_ver semantics_algebra.renaming_invert_wf semantics_algebra_axioms wf_rename_inv_other wf_renaming_order)
    then have main: "ver Pr {?b} s \<and> sem Pr {?b} s >> sem Pr {?a} s"
      by (meson assms(1) semantics_algebra.smono_def semantics_algebra_axioms smonoOut_singleton ssafeMono_singleton)
    then have "ver Pr {b} ?s"
      by (metis assms rename_inv_def_state renaming_invert_wf rename_ver)
    moreover have "rename_state ?a t = a"
      by (metis assms(2) rename_inv_def_state renaming_invert_wf)
    moreover have "rename_state ?b t = b"
      by (metis assms(2) rename_inv_def_state renaming_invert_wf)
    ultimately have "sem Pr {b} ?s >> sem Pr {a} ?s"
      using asm assms(2) assms(3) assms(4) main rename_sem rename_set_smaller
      by (metis \<open>rename_state a (rename_inv t) << rename_state b (rename_inv t) \<and> ver Pr {rename_state a (rename_inv t)} s \<and> (\<exists>d\<in>D. rename_state b (rename_inv t) << d)\<close>)
    then show "ver Pr {b} ?s \<and> sem Pr {b} ?s >> sem Pr {a} ?s"
      using \<open>ver Pr {b} (rename s t)\<close> by blast
  qed
  then show ?thesis
    by (meson semantics_algebra.ssafeMono_singleton semantics_algebra_axioms smonoOut_singleton smono_def)
qed

lemma rename_singleton:
  "rename_set {a} t = {rename_state a t}"
  by simp

lemma rename_sem_set:
  assumes "wf_renaming t"
      and "wf_program Pr"
      and "wf_stmt Pr s"
      and "ver Pr (rename_set A t) s"
  shows "sem Pr (rename_set A t) s = rename_set (sem Pr A (rename s (rename_inv t))) t" (is "?a = ?b")
proof -
  let ?t = "rename_inv t"
  let ?s = "rename s ?t"
  have "?a \<subseteq> ?b"
  proof (rule subsetI)
    fix x assume "x \<in> ?a"
    then obtain a where "a \<in> A" "x \<in> sem Pr {rename_state a t} s" by auto
    let ?a = "rename_state a t"
    have "s = rename ?s t"
      by (metis assms renaming_invert renaming_invert_wf)
    then have "sem Pr {rename_state a t} s = rename_set (sem Pr {a} ?s) t"
    proof -
      have "ver Pr {rename_state a t} s" 
        using assms(4) 
        by (meson \<open>a \<in> A\<close> assms(1) semantics_algebra.v_singleton semantics_algebra_axioms simple_state_in_set)
      then show ?thesis
        using Set.set_insert \<open>s = rename (rename s (rename_inv t)) t\<close> \<open>x \<in> sem Pr {rename_state a t} s\<close> assms cSup_singleton get_S.simps(2) image_empty image_insert insert_not_empty rename_sem semantics_algebra.rename_ver semantics_algebra.sem.simps semantics_algebra.ver_def semantics_algebra_axioms singletonD
        by (smt renaming_invert_wf wf_stmt_wf_renaming)
    qed
    then show "x \<in> ?b"
      using \<open>a \<in> A\<close> \<open>x \<in> sem Pr {rename_state a t} s\<close> by auto
  qed
  moreover have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix x assume "x \<in> ?b"
    then obtain a where "a \<in> A" "x \<in> rename_set (sem Pr {a} ?s) t" by auto
    have "s = rename ?s t"
      by (metis assms renaming_invert renaming_invert_wf)
    then have "sem Pr {rename_state a t} s = rename_set (sem Pr {a} ?s) t"
    proof -
      have "ver Pr {rename_state a t} (rename ?s t)" 
        by (metis \<open>a \<in> A\<close> \<open>s = rename (rename s (rename_inv t)) t\<close> assms(1) assms(4) member_rename_set_inv rename_inv_def_state v_singleton)
      then have "sem Pr {rename_state a t} (rename ?s t) = rename_set (sem Pr {a} ?s) t"
        using assms(1) assms(2) assms(3) rename_all rename_ver renaming_invert_wf wf_stmt_wf_renaming by blast
      then show ?thesis
        using \<open>s = rename (rename s (rename_inv t)) t\<close> by auto
    qed
    then show "x \<in> ?a"
      using \<open>a \<in> A\<close> \<open>x \<in> rename_set (sem Pr {a} (rename s (rename_inv t))) t\<close> by auto
  qed
  ultimately show ?thesis by blast
qed



lemma framingI:
  assumes "mono Pr A s"
      and "(\<And>a r. (\<exists>s b. Some s = Some a \<oplus> Some r \<and> s << b \<and> b \<in> A) \<and> ver Pr {a} s \<and> set (modif s) \<inter> \<sigma> r = {} \<Longrightarrow> sem Pr ({a} \<oplus>\<oplus> {r}) s >> sem Pr {a} s \<oplus>\<oplus> {r})"
    shows "framing Pr A s"
  using assms(1) assms(2) framing.simps mono_smono by blast

lemma assume_false_smono:
  "smono Pr A (Assume lfalse)"
proof -
  have "ssafeMono Pr A (Assume lfalse)"
    by (simp add: can_read_false ssafeMono_singleton ver_def)
  moreover have "smonoOut Pr A (Assume lfalse)"
    by (metis equals0D greaterI lfalse_def sem_assume_false smonoOutI)
  ultimately show ?thesis
    by (simp add: smono_def)
qed

lemma inhale_smono:
  assumes "wf_assert P"
  shows "smono Pr A (Inhale P)"
proof -
  have "ssafeMono Pr A (Inhale P)"
    by (simp add: assms wf_assert_monoIn(1))
  moreover have "smonoOut Pr A (Inhale P)"
    using calculation plus_and_bigger_set sem_inhale ssafeMono_def smonoOut_def ver_inhale by auto
  ultimately show ?thesis using local.smono_def by blast
qed

lemma exhale_elem:
  assumes "ver Pr {a} (Exhale P)"
    shows "sa \<in> sem Pr {a} (Exhale P) \<longleftrightarrow> (\<exists>i r. Some a = Some i \<oplus> Some r \<and> i \<in> Inh P \<and> Some sa = s_core i \<oplus> Some r)" (is "?a \<longleftrightarrow> ?b")
  using assms exhale_verif
  by (smt mem_Collect_eq semantics_algebra.sem_exhale semantics_algebra_axioms)

lemma havoc_smono:
  "smono Pr A (Havoc x)"
proof -
  let ?s = "Havoc x"
  have "ssafeMono Pr A (Havoc x)"
  proof -
    have "\<And>a b. b << a \<and> ver Pr {b} ?s \<Longrightarrow> ver Pr {a} ?s"
    proof -
      fix a b assume "b << a \<and> ver Pr {b} ?s"
      then obtain c where "Some a = Some b \<oplus> Some c" using smaller_def by blast
      then have "\<sigma> b \<subseteq> \<sigma> a" by (simp add: store_add)
      then show "ver Pr {a} ?s" using \<open>b << a \<and> ver Pr {b} (Havoc x)\<close> ver_havoc by auto
    qed
    then show ?thesis using ssafeMono_singleton by blast
  qed
  moreover have "smonoOut Pr A (Havoc x)"
  proof -
    have "\<And>a b. b << a \<and> ver Pr {b} ?s \<and> (\<exists>x \<in> A. a << x) \<Longrightarrow> sem Pr {a} ?s >> sem Pr {b} ?s"
    proof -
      fix a b assume asm: "b << a \<and> ver Pr {b} ?s \<and> (\<exists>x \<in> A. a << x)"
      obtain "sem Pr {a} ?s = {h_comp a x} \<oplus>\<oplus> h x" "sem Pr {b} ?s = {h_comp b x} \<oplus>\<oplus> h x"
        using asm calculation sem_havoc ssafeMono_singleton by blast
      then show "sem Pr {a} ?s >> sem Pr {b} ?s" by (metis asm bigger_set_def
            plus_and_bigger_set h_comp_grows semantics_algebra_axioms singletonD singletonI)
    qed
    then show ?thesis by (simp add: smonoOut_singleton)
  qed
  ultimately show ?thesis by (simp add: local.smono_def)
qed

lemma smono_out_equiv:
  assumes "\<And>\<phi>. ver Pr {\<phi>} s2 \<Longrightarrow> sem Pr {\<phi>} s1 = sem Pr {\<phi>} s2"
      and "smonoOut Pr A s1"
      and "\<And>\<phi>. ver Pr {\<phi>} s2 \<Longrightarrow> ver Pr {\<phi>} s1"
      and "ssafeMono Pr A s2"
    shows "smonoOut Pr A s2"
  using assms(1) assms(2) assms(3) assms(4) smonoOut_singleton ssafeMono_singleton by smt

(*
lemma method_smono:
  assumes "wf_program Pr"
      and "wf_stmt Pr (MethodCall y m x)"
    shows "smono Pr D (MethodCall y m x)"
proof -
  let ?m = "MethodCall y m x"
  have "\<And>a b. b << a \<and> ver Pr {b} ?m \<and> a \<in> D \<Longrightarrow> ver Pr {a} ?m \<and> sem Pr {a} ?m >> sem Pr {b} ?m"
  proof -
    fix a b assume asm: "b << a \<and> ver Pr {b} ?m \<and> a \<in> D"
    then obtain args ret P Q s where basic: "get_method Pr m = Some (m, args, ret, P, Q, s)"
      using assms(2) simple_method_exists by blast
    then have "wf_method Pr (m, args, ret, P, Q, s)"
      using assms(1) wf_program_method by blast
    then have "set x \<union> set y \<subseteq> \<sigma> b"
      using asm ver_method_real basic by auto
    moreover have "\<sigma> b \<subseteq> \<sigma> a"
      using asm smaller_def store_add by auto
    ultimately have "set x \<union> set y \<subseteq> \<sigma> a" by blast
    let ?s1 = "Exhale (rename_pred P (args @ ret, x @ y, [], []))"
    let ?s2 = "Havoc y"
    let ?s3 = "Inhale (rename_pred Q (args @ ret, x @ y, [], []))"
    have "ver Pr {a} (?s1 ; ?s2 ; ?s3) \<and> sem Pr {a} (?s1 ; ?s2 ; ?s3) >> sem Pr {b} (?s1 ; ?s2 ; ?s3)"
    proof -
      have "smono Pr D (Exhale (rename_pred P (args @ ret, x @ y, [], [])); Havoc y; Inhale (rename_pred Q (args @ ret, x @ y, [], [])))"
      proof -
        have "wf_assert (rename_pred P (args @ ret, x @ y, [], []))"
          by (meson \<open>wf_method Pr (m, args, ret, P, Q, s)\<close> assms(1) assms(2) basic same_wf_rename semantics_algebra.wf_method.simps semantics_algebra_axioms wf_wf_renaming(2))
        then have "smono Pr D ?s1"
          using exhale_smono by blast
        moreover have "smono Pr (sem Pr D ?s1) ?s2"
          using havoc_smono by blast
        ultimately have "smono Pr D (?s1 ; ?s2)"
          using mono_comp mono_smono by blast
        moreover have "wf_assert (rename_pred Q (args @ ret, x @ y, [], []))"
          using \<open>wf_method Pr (m, args, ret, P, Q, s)\<close> assms(2) basic same_wf_rename by auto
        then have "smono Pr (sem Pr D (?s1 ; ?s2)) ?s3"
          using inhale_smono by blast
        ultimately show "smono Pr D (?s1 ; ?s2 ; ?s3)"
          using mono_comp mono_smono by blast
      qed
      then show ?thesis
        by (meson asm basic semantics_algebra.ver_method_real semantics_algebra_axioms smonoOut_singleton smono_def ssafeMono_singleton)
    qed
    then show "ver Pr {a} ?m \<and> sem Pr {a} ?m >> sem Pr {b} ?m"
      using \<open>set x \<union> set y \<subseteq> \<sigma> a\<close> asm basic ver_method_real by auto
  qed
  then show ?thesis
    by (meson mono_smono smonoOut_singleton smono_def ssafeMono_singleton)
qed
*)

fun ver_program_aux :: "('a, 'b, 'c) program \<Rightarrow> ('a, 'b, 'c) program \<Rightarrow> bool" where
  "ver_program_aux Pr [] \<longleftrightarrow> True"
| "ver_program_aux Pr ((_, args, ret, P, Q, s) # q) \<longleftrightarrow> ver Pr {u} (Var (args @ ret) ; Inhale P ; s ; Exhale Q) \<and> ver_program_aux Pr q"

fun ver_program :: "('a, 'b, 'c) program \<Rightarrow> bool" where
  "ver_program Pr \<longleftrightarrow> ver_program_aux Pr Pr"


lemma first_stmt_mono:
  "mono Pr {u} s" 
proof (rule monoI)
  fix a b assume asm: "b << a \<and> ver Pr {b} s \<and> (\<exists>x\<in>{u}. a << x)"
  then obtain "a = u" "b = u"
    by (metis empty_iff insert_iff local.antisym u_smaller)
  then show "ver Pr {a} s \<and> sem Pr {a} s >> sem Pr {b} s"
    using asm subset_smaller by auto
qed

end

end
