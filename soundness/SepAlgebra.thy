theory SepAlgebra
  imports Main
begin

type_synonym 'a assertion = "'a \<Rightarrow> bool option"

subsection \<open>Preliminary separation algebra\<close>

locale commutative_monoid =
  fixes orig_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  fixes u :: "'a"
  assumes orig_comm: "orig_plus a b = orig_plus b a"
      and asso1: "Some ab = orig_plus a b \<and> Some bc = orig_plus b c \<Longrightarrow> orig_plus ab c = orig_plus a bc"
      and asso2: "Some ab = orig_plus a b \<and> None = orig_plus b c \<Longrightarrow> None = orig_plus ab c"
      and asso3: "None = orig_plus a b \<and> Some bc = orig_plus b c \<Longrightarrow> None = orig_plus a bc"
      and orig_neutral: "orig_plus a u = Some a"
begin

fun plus :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" (infixl "\<oplus>" 60) where
  "Some a \<oplus> Some b = orig_plus a b"
| "_ \<oplus> _ = None"

definition defined :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "##" 60)
  where "defined a b \<longleftrightarrow> (\<not> Option.is_none (Some a \<oplus> Some b))"

definition smaller :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "<<" 50) where
  "smaller a b \<longleftrightarrow> (\<exists>c. Some b = Some a \<oplus> Some c)"

lemma commutative:
  "a \<oplus> b = b \<oplus> a"
  by (metis option.exhaust_sel orig_comm plus.simps(1) plus.simps(2) plus.simps(3))

lemma associative:
  "(a \<oplus> b) \<oplus> c = a \<oplus> (b \<oplus> c)"
proof (cases "\<exists>aa bb cc. a = Some aa \<and> b = Some bb \<and> c = Some cc")
  case True
  then obtain aa bb cc where "a = Some aa \<and> b = Some bb \<and> c = Some cc" by blast
  then show ?thesis
  proof (cases "Some aa \<oplus> Some bb")
    case None
    then have "(a \<oplus> b) \<oplus> c = None"
      by (simp add: \<open>a = Some aa \<and> b = Some bb \<and> c = Some cc\<close>)
    then show ?thesis
    proof (cases "Some bb \<oplus> Some cc")
      case None
      then show ?thesis
        using \<open>a = Some aa \<and> b = Some bb \<and> c = Some cc\<close> \<open>a \<oplus> b \<oplus> c = None\<close> by auto
    next
      case (Some ab)
      then show ?thesis
        by (metis None \<open>a = Some aa \<and> b = Some bb \<and> c = Some cc\<close> \<open>a \<oplus> b \<oplus> c = None\<close> asso3 plus.simps(1))
    qed
  next
    case (Some ab)
    then have "Some ab = Some aa \<oplus> Some bb" by simp
    then show ?thesis
    proof (cases "Some bb \<oplus> Some cc")
      case None
      then show ?thesis
        by (metis Some \<open>a = Some aa \<and> b = Some bb \<and> c = Some cc\<close> asso2 plus.simps(1) plus.simps(3))
    next
      case (Some bc)
      then show ?thesis
        by (metis \<open>Some ab = Some aa \<oplus> Some bb\<close> \<open>a = Some aa \<and> b = Some bb \<and> c = Some cc\<close> plus.simps(1) commutative_monoid.asso1 commutative_monoid_axioms)
    qed
  qed
next
  case False
  then show ?thesis
    by auto
qed

lemma neutral:
  "a \<oplus> Some u = a" by (metis option.distinct(1) option.sel orig_neutral plus.elims)

lemma smaller_refl:
  "a << a"
  by (metis neutral smaller_def)

lemma smaller_trans:
  assumes "a << b"
      and "b << c"
    shows "a << c"
proof -
  obtain ab bc where "Some b = Some ab \<oplus> Some a" "Some c = Some bc \<oplus> Some b"
    by (metis assms(1) assms(2) commutative smaller_def)
  then have "Some c = Some bc \<oplus> (Some ab \<oplus> Some a)"
    using associative by auto
  then show ?thesis
    by (metis associative commutative option.discI option.exhaust_sel plus.simps(2) smaller_def)
qed

definition pure :: "'a \<Rightarrow> bool" where
  "pure \<phi> \<longleftrightarrow> Some \<phi> \<oplus> Some \<phi> = Some \<phi>"

definition pure_set :: "'a \<Rightarrow> 'a set" where
  "pure_set \<phi> = {\<phi>'. pure \<phi>' \<and> \<phi>' << \<phi>}"

definition core :: "'a \<Rightarrow> 'a" ("|_|")
  where "|\<phi>| = the (Finite_Set.fold (\<oplus>) (Some u) (Some ` (pure_set \<phi>)))"

lemma pure_smaller_ok:
  assumes "p << \<phi>"
      and "pure p"
    shows "Some \<phi> = Some \<phi> \<oplus> Some p"
  by (smt assms(1) assms(2) associative commutative pure_def smaller_def)

lemma pure_add:
  assumes "pure a"
  assumes "pure b"
  assumes "a ## b"
  shows "pure (the (Some a \<oplus> Some b))"
proof -
  have "Some (the (Some a \<oplus> Some b)) = Some a \<oplus> Some b"
    by (metis (no_types) Option.is_none_def assms(3) defined_def option.collapse)
  then show ?thesis
    by (metis (full_types) assms(1) assms(2) associative commutative pure_def)
qed

lemma pure_set_stable_add:
  assumes "a \<in> pure_set \<phi>"
      and "b \<in> pure_set \<phi>"
      and "Some c = Some a \<oplus> Some b"
    shows "c \<in> pure_set \<phi>"
proof -
  have "pure c"
    by (metis assms(1) assms(2) assms(3) defined_def is_none_code(2) mem_Collect_eq option.sel pure_add pure_set_def)
  obtain "Some \<phi> = Some \<phi> \<oplus> Some a" and "Some \<phi> = Some \<phi> \<oplus> Some b"
    using assms(1) assms(2) pure_smaller_ok pure_set_def commutative_monoid_axioms by fastforce
  then have "Some \<phi> = Some \<phi> \<oplus> Some a \<oplus> Some b" by presburger
  then have "c << \<phi>" by (metis assms(3) associative commutative smaller_def)
  then show ?thesis by (simp add: \<open>pure c\<close> pure_set_def)
qed

lemma pure_u [simp]: "pure u" by (simp add: orig_neutral pure_def)

lemma u_smaller [simp]: "u << \<phi>" by (simp add: commutative neutral smaller_def)

lemma empty_in_pure:
  "u \<in> pure_set \<phi>"
  by (simp add: pure_set_def)

definition s_core :: "'a \<Rightarrow> 'a option" where "s_core x = Some |x|"

end

subsection \<open>Separation algebra\<close>

locale sep_algebra = commutative_monoid +
  fixes C :: "'a \<Rightarrow> 'a"
  fixes \<sigma> :: "'a \<Rightarrow> 'b set"

  (* Algebra *)
  assumes finiteness: "finite {\<phi>'. pure \<phi>' \<and> \<phi>' << \<phi>}"
      and positivity: "Some a \<oplus> Some b = Some u \<Longrightarrow> a = u"
      and partially_cancellative: "Some (C \<phi>) \<oplus> Some a = Some (C \<phi>) \<oplus> Some b \<Longrightarrow> a = b"
      and unique_c: "Some \<phi> = Some |\<phi>| \<oplus> Some \<phi>' \<and> |\<phi>'| = u \<longleftrightarrow> \<phi>' = C \<phi>"

  (* STORE *)
      and store_C_empty: "\<sigma> (C \<phi>) = {}"
      and store_pure: "\<sigma> \<phi> = \<sigma> |\<phi>|"
      and store_add: "Some a = Some c \<oplus> Some d \<Longrightarrow> \<sigma> a = \<sigma> c \<union> \<sigma> d"
      and compatible_stores: "a ## b \<Longrightarrow> pure a \<Longrightarrow> \<sigma> a \<subseteq> \<sigma> b \<Longrightarrow> a << b"
      and unique_store_exists: "var \<in> \<sigma> a \<Longrightarrow> (\<exists>c. \<sigma> c = {var} \<and> c << a)"
      and defined_disjoint_store: "\<sigma> a \<inter> \<sigma> b = {} \<Longrightarrow> pure a \<Longrightarrow> a ## b"
begin

lemma decompo: "Some \<phi> = Some |\<phi>| \<oplus> Some (C \<phi>)"
  using unique_c by blast

lemma store_empty: "\<sigma> u = {}"
  by (metis decompo neutral positivity sep_algebra.unique_c sep_algebra_axioms store_C_empty)

lemma pure_u:
  "|u| = u"
  by (metis decompo positivity)

definition some_core :: "'a \<Rightarrow> 'a option" where
  "some_core \<phi> = (Finite_Set.fold (\<oplus>) (Some u) (Some ` (pure_set \<phi>)))"

lemma commut_comp: "\<And>y x. (\<oplus>) y \<circ> (\<oplus>) x = (\<oplus>) x \<circ> (\<oplus>) y"
  apply (rule ext)
proof -
  fix y x xa
  have "((\<oplus>) y \<circ> (\<oplus>) x) xa = (\<oplus>) y (x \<oplus> xa)" by simp
  then have "... = y \<oplus> (x \<oplus> xa)" by simp
  then have "... = x \<oplus> (y \<oplus> xa)" using associative commutative by auto
  then have "... = ((\<oplus>) x \<circ> (\<oplus>) y) xa" by simp
  then show "((\<oplus>) y \<circ> (\<oplus>) x) xa = ((\<oplus>) x \<circ> (\<oplus>) y) xa"
    by (metis \<open>y \<oplus> (x \<oplus> xa) = x \<oplus> (y \<oplus> xa)\<close> comp_apply)
qed

interpretation add_pure: comp_fun_commute "plus"
  by unfold_locales (simp add: commut_comp)

lemma "fold_graph (\<oplus>) (Some u) (Some ` pure_set \<phi>) (some_core \<phi>)"
proof -
  let ?A = "Some ` pure_set \<phi>"
  have "finite ?A" by (simp add: finiteness pure_set_def)
  then have "fold_graph (\<oplus>) (Some u) ?A (Finite_Set.fold (\<oplus>) (Some u) ?A)"
    using add_pure.fold_graph_fold by blast
  then show ?thesis by (simp add: some_core_def)
qed

lemma "|\<phi>| = the (some_core \<phi>)" by (simp add: core_def some_core_def)

lemma pure_set_u: "pure_set u = {u}"
proof -
  have "\<And>x. x << u \<Longrightarrow> x = u" using positivity smaller_def by auto
  moreover have "pure u" by simp
  ultimately show ?thesis using pure_set_def by auto
qed

lemma some_core_u:
  "some_core u = Some u"
by (simp add: neutral pure_set_u some_core_def)

definition some_prop :: "'a \<Rightarrow> 'a option set \<Rightarrow> 'a option \<Rightarrow> bool" where
  "some_prop \<phi> S s \<longleftrightarrow> (S \<subseteq> Some ` pure_set \<phi> \<longrightarrow> (S = {} \<and> s = Some u) \<or> (s \<in> Some ` pure_set \<phi> \<and> (\<forall>s' \<in> S. the s' << the s)))"

lemma some_prop_proof:
  "some_prop \<phi> (Some ` pure_set \<phi>) (some_core \<phi>)"
proof -
  have "fold_graph (\<oplus>) (Some u) (Some ` pure_set \<phi>) (some_core \<phi>)"
    by (simp add: add_pure.comp_fun_commute_axioms comp_fun_commute.fold_graph_fold finiteness pure_set_def some_core_def)
  moreover have "some_prop \<phi> {} (Some u)" using some_prop_def by blast
  moreover have "\<And>x A y. x \<notin> A \<and> fold_graph (\<oplus>) (Some u) A y \<and> some_prop \<phi> A y \<Longrightarrow> some_prop \<phi> (insert x A) (x \<oplus> y)"
  proof -
    fix x A y
    assume "x \<notin> A \<and> fold_graph (\<oplus>) (Some u) A y \<and> some_prop \<phi> A y"
    then show "some_prop \<phi> (insert x A) (x \<oplus> y)"
    proof (cases "(insert x A) \<subseteq> Some ` pure_set \<phi>")
      case True
      then show ?thesis
      proof (cases "A = {}")
        case True
        then show ?thesis
          by (metis \<open>x \<notin> A \<and> fold_graph (\<oplus>) (Some u) A y \<and> some_prop \<phi> A y\<close> empty_fold_graphE insert_subset neutral sep_algebra.some_prop_def sep_algebra_axioms singletonD smaller_refl)
      next
        case False
        then have "y \<in> Some ` pure_set \<phi> \<and> (\<forall>s' \<in> A. the s' << the y)"
          using True \<open>x \<notin> A \<and> fold_graph (\<oplus>) (Some u) A y \<and> some_prop \<phi> A y\<close> some_prop_def by auto
        moreover obtain "A \<subseteq> Some ` pure_set \<phi>" "x \<in> Some ` pure_set \<phi>" using True by blast
        then obtain xx where "x = Some xx" "xx \<in> pure_set \<phi>" by blast
        moreover obtain yy where "y = Some yy" "yy \<in> pure_set \<phi>" using \<open>A \<subseteq> Some ` pure_set \<phi>\<close> calculation(1) by blast
        then obtain zz where "Some zz = Some xx \<oplus> Some yy"
        proof -
          assume a1: "\<And>zz. Some zz = Some xx \<oplus> Some yy \<Longrightarrow> thesis"
          have "\<forall>a aa. a \<notin> pure_set aa \<or> Some aa = orig_plus aa a"
            using commutative_monoid.pure_set_def commutative_monoid_axioms pure_smaller_ok by fastforce
          then show ?thesis
            using a1 by (metis (lifting) \<open>y = Some yy\<close> \<open>yy \<in> pure_set \<phi>\<close> associative calculation(2) calculation(3) option.exhaust orig_comm plus.simps(1) plus.simps(2))
        qed
        then have "Some zz \<in> Some ` pure_set \<phi>" by (meson \<open>yy \<in> pure_set \<phi>\<close> calculation(3) image_eqI pure_set_stable_add)
        moreover have "xx << zz" using \<open>Some zz = Some xx \<oplus> Some yy\<close> smaller_def by blast
        moreover have "\<And>s' . s' \<in> A \<Longrightarrow> the s' << zz"
        proof -
          fix s' assume "s' \<in> A"
          then have "the s' << yy" using \<open>y = Some yy\<close> calculation(1) by auto
          then show "the s' << zz"
            by (metis \<open>Some zz = Some xx \<oplus> Some yy\<close> commutative smaller_def smaller_trans)
        qed
        ultimately have "\<forall>s' \<in> (insert x A). the s' << zz" by simp
        then show ?thesis
          by (metis (mono_tags, lifting) \<open>Some zz = Some xx \<oplus> Some yy\<close> \<open>Some zz \<in> Some ` pure_set \<phi>\<close> \<open>x = Some xx\<close> \<open>y = Some yy\<close> option.sel sep_algebra.some_prop_def sep_algebra_axioms)
      qed
    next
      case False
      then show ?thesis using some_prop_def by auto
    qed
  qed
  ultimately show "some_prop \<phi> (Some ` pure_set \<phi>) (some_core \<phi>)" using fold_graph.induct[of "(\<oplus>)" "Some u" "Some ` (pure_set \<phi>)" "some_core \<phi>" "some_prop \<phi>"]
    by blast
qed

lemma core_is_max_uni:
  "|\<phi>| \<in> pure_set \<phi> \<and> (\<forall>x \<in> pure_set \<phi>. x << |\<phi>| )"
proof -
  have "some_core \<phi> \<in> Some ` pure_set \<phi> \<and> (\<forall>x \<in> pure_set \<phi>. x << the (some_core \<phi>))"
  proof -
    have "some_prop \<phi> (Some ` pure_set \<phi>) (some_core \<phi>)" using some_prop_proof by auto
    then have "(Some ` pure_set \<phi> \<subseteq> Some ` pure_set \<phi> \<longrightarrow> (Some ` pure_set \<phi> = {} \<and> some_core \<phi> = Some u) \<or> (some_core \<phi> \<in> Some ` pure_set \<phi> \<and> (\<forall>s' \<in> Some ` pure_set \<phi>. the s' << the (some_core \<phi>))))"
      by (simp add: some_prop_def)
    then have "(Some ` pure_set \<phi> = {} \<and> some_core \<phi> = Some u) \<or> (some_core \<phi> \<in> Some ` pure_set \<phi> \<and> (\<forall>s' \<in> Some ` pure_set \<phi>. the s' << the (some_core \<phi>)))"
      by blast
    moreover have "pure_set \<phi> \<noteq> {}" using empty_in_pure by blast
    then have "Some ` pure_set \<phi> \<noteq> {}" by simp
    ultimately have "some_core \<phi> \<in> Some ` pure_set \<phi> \<and> (\<forall>s' \<in> Some ` pure_set \<phi>. the s' << the (some_core \<phi>))"
      by linarith
    then show ?thesis by auto
  qed
  moreover have "some_core \<phi> = Some |\<phi>|" using calculation core_def some_core_def by auto
  ultimately show ?thesis by (simp add: image_iff smaller_def)
qed

lemma core_is_max:
  "\<phi>' = |\<phi>| \<longleftrightarrow> (\<phi>' \<in> pure_set \<phi> \<and> (\<forall>\<phi>'' \<in> pure_set \<phi>. \<phi>'' << \<phi>'))" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b" using core_is_max_uni by blast
  moreover have "?b \<Longrightarrow> ?a"
    by (metis (no_types, lifting) commutative core_is_max_uni mem_Collect_eq option.inject commutative_monoid.pure_smaller_ok commutative_monoid_axioms pure_set_def)
  ultimately show ?thesis by blast
qed

lemma sum_pure:
  assumes "pure a"
      and "pure b"
      and "Some c = Some a \<oplus> Some b"
    shows "pure c"
  by (metis assms(1) assms(2) assms(3) is_none_code(2) option.sel commutative_monoid.defined_def commutative_monoid_axioms pure_add)

lemma add_trans:
  assumes "a << aa"
      and "b << bb"
      and "Some cc = Some aa \<oplus> Some bb"
      and "Some c = Some a \<oplus> Some b"
    shows "c << cc"
proof -
  obtain aaa where "Some aa = Some a \<oplus> Some aaa" using assms(1) smaller_def by blast
  obtain bbb where "Some bb = Some b \<oplus> Some bbb" using assms(2) smaller_def by blast
  then have "Some cc = Some a \<oplus> Some aaa \<oplus> Some b \<oplus> Some bbb"
    by (simp add: \<open>Some aa = Some a \<oplus> Some aaa\<close> assms(3) associative)
  then have "Some cc = Some c \<oplus> Some aaa \<oplus> Some bbb" by (metis assms(4) associative commutative)
  then show ?thesis by (metis associative plus.elims smaller_def)
qed

lemma pure_set_finite:
  "finite (pure_set \<phi>)"
  by (simp add: finiteness pure_set_def)

definition s_C :: "'a \<Rightarrow> 'a option" where "s_C x = Some (C x)"

lemma core_properties:
  shows "pure |\<phi>|"
    and "|\<phi>| << \<phi>"
    and "pure \<phi> \<longleftrightarrow> \<phi> = |\<phi>|"
proof -
  show "pure |\<phi>|" using core_is_max pure_set_def by auto
  show "|\<phi>| << \<phi>" using core_is_max pure_set_def by auto
  show "pure \<phi> \<longleftrightarrow> \<phi> = |\<phi>|" (is "?a \<longleftrightarrow> ?b")
  proof -
    have "?b \<longrightarrow> ?a" using \<open>pure |\<phi>|\<close> by auto
    moreover have "?a \<Longrightarrow> ?b"
    proof -
      assume "?a"
      then have "\<phi> \<in> pure_set \<phi>" by (simp add: pure_set_def smaller_refl)
      then show "?b" by (simp add: core_is_max pure_set_def)
    qed
    then show ?thesis using calculation by blast
  qed
qed

lemma not_pure_core:
  "\<not> pure \<phi> \<longleftrightarrow> \<phi> \<noteq> |\<phi>|" (is "?a \<longleftrightarrow> ?b")
  using core_properties(3) by auto

definition add_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<oplus>\<oplus>" 60) where
  "A \<oplus>\<oplus> B = {the (Some a \<oplus> Some b) | a b. a \<in> A \<and> b \<in> B \<and> a ## b}"

lemma elem_add_set:
  "x \<in> A \<oplus>\<oplus> B \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some x = Some a \<oplus> Some b)"
  by (smt defined_def is_none_code(2) is_none_simps(1) mem_Collect_eq option.expand option.sel sep_algebra.add_set_def sep_algebra_axioms)

lemma simple_set_add_comm:
  "A \<oplus>\<oplus> B = B \<oplus>\<oplus> A"
proof -
  have "\<And>A B. A \<oplus>\<oplus> B \<subseteq> B \<oplus>\<oplus> A"
  proof (rule subsetI)
    fix A B x assume "x \<in> A \<oplus>\<oplus> B"
    obtain a b where "a \<in> A" "b \<in> B" "a ## b" "x = the (Some a \<oplus> Some b)" using \<open>x \<in> A \<oplus>\<oplus> B\<close> add_set_def by auto
    then have "Some x = Some a \<oplus> Some b" by (simp add: Option.is_none_def defined_def)
    then obtain "b ## a" "x = the (Some b \<oplus> Some a)"
      using \<open>a ## b\<close> \<open>x = the (Some a \<oplus> Some b)\<close> commutative defined_def by auto
    then show "x \<in> B \<oplus>\<oplus> A"
      by (metis (mono_tags, lifting) CollectI \<open>a \<in> A\<close> \<open>b \<in> B\<close> add_set_def)
  qed
  then show ?thesis by blast
qed

lemma core_inv:
  "||\<phi>|| = |\<phi>|"
  using core_properties(1) not_pure_core by auto

lemma decompo_new_plus:
  "Some \<phi> = s_core \<phi> \<oplus> s_C \<phi>"
  using decompo s_C_def s_core_def by fastforce

lemma c_empty_core: "|C \<phi>| = u" (is "?x = u")
proof -
  have "\<sigma> ?x = {}" 
    using store_C_empty store_pure by blast
  moreover have "pure ?x" 
    by (simp add: core_properties(1))
  then have "?x << u" 
    by (simp add: calculation compatible_stores defined_disjoint_store)
  then show ?thesis 
    using positivity smaller_def by auto
qed

lemma properties_c:
  shows "a = b \<longleftrightarrow> |a| = |b| \<and> C a = C b"
    and "C (C \<phi>) = C \<phi>"
  apply (metis decompo option.inject)
  by (metis c_empty_core commutative commutative_monoid.neutral commutative_monoid_axioms unique_c)

lemma definedness [simp]:
  assumes "a ## b"
  shows "C a ## b"
    and "core a ## b"
    and "b ## a"
  apply (metis (full_types) Option.is_none_def add_pure.comp_fun_commute_axioms assms commutative comp_fun_commute.fun_left_comm decompo defined_def plus.simps(3))
  apply (smt Option.is_none_def add_pure.comp_fun_commute_axioms assms commutative comp_fun_commute.fun_left_comm core_properties(1) core_properties(2) defined_def plus.simps(3) pure_smaller_ok)
  by (metis assms commutative defined_def)

definition bigger_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl ">>" 50) where
  "A >> B \<longleftrightarrow> (\<forall>a \<in> A. \<exists>b \<in> B. b << a)"

lemma rel_bigger_add_set:
  assumes "A = B \<oplus>\<oplus> D"
  shows "A >> B"
proof -
  have "\<And>a. a \<in> A \<Longrightarrow> (\<exists>b\<in>B. b << a)"
  proof -
    fix a assume "a \<in> A"
    obtain b d where "Some a = Some b \<oplus> Some d" "b \<in> B"
      using \<open>a \<in> A\<close> assms elem_add_set by auto
    then show "\<exists>b\<in>B. b << a" using smaller_def by auto
  qed
  then show ?thesis by (simp add: bigger_set_def)
qed

lemma defined_trans_plus:
  assumes "Some a = Some b \<oplus> Some c \<oplus> Some d"
  shows "c ## d"
  by (metis Option.is_none_def assms associative defined_def option.simps(3) commutative_monoid.plus.simps(3) commutative_monoid_axioms)

lemma neutral_parts:
  shows "|u| = u"
    and "C u = u"
  using core_properties(3) pure_u apply auto[1]
  by (metis c_empty_core properties_c(2) pure_u sep_algebra.properties_c(1) sep_algebra_axioms)

lemma plus_and_bigger_set:
  assumes "A >> B"
  shows "(A \<oplus>\<oplus> D) >> (B \<oplus>\<oplus> D)"
proof -
  have "\<And>ad. (ad \<in> A \<oplus>\<oplus> D) \<Longrightarrow> (\<exists>bd \<in> B \<oplus>\<oplus> D. bd << ad)"
  proof -
    fix ad assume "ad \<in> A \<oplus>\<oplus> D"
    then obtain a d where "a \<in> A" "d \<in> D" "Some ad = Some a \<oplus> Some d" using elem_add_set by auto
    then obtain b where "b \<in> B" "b << a" using assms bigger_set_def by blast
    then obtain c where "Some a = Some b \<oplus> Some c" using smaller_def by blast
    then have "Some ad = Some b \<oplus> Some c \<oplus> Some d" by (simp add: \<open>Some ad = Some a \<oplus> Some d\<close>)
    moreover obtain bd where "Some bd = Some b \<oplus> Some d"
      by (metis \<open>Some ad = Some a \<oplus> Some d\<close> \<open>\<And>thesis. (\<And>c. Some a = Some b \<oplus> Some c \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> asso2 commutative option.exhaust_sel plus.simps(1))
    ultimately have "bd << ad" by (metis associative commutative smaller_def)
    then show "\<exists>bd \<in> B \<oplus>\<oplus> D. bd << ad"
      using \<open>Some bd = Some b \<oplus> Some d\<close> \<open>b \<in> B\<close> \<open>d \<in> D\<close> elem_add_set by blast
  qed
  then show ?thesis by (simp add: bigger_set_def)
qed

lemma simple_set_add:
  assumes "Some a = Some b \<oplus> Some c"
  shows "{b} \<oplus>\<oplus> {c} = {a}" (is "?s = ?a")
proof -
  have "?a \<subseteq> ?s"
    by (smt CollectI assms is_none_code(2) option.sel add_set_def defined_def sep_algebra_axioms singletonD singletonI subsetI)
  moreover have "?s \<subseteq> ?a"
    by (smt CollectD add_set_def assms insertCI option.sel singletonD subsetI)
  ultimately show ?thesis by blast
qed

lemma set_add_elem:
  assumes "x \<in> A \<oplus>\<oplus> B"
  shows "\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some x = Some a \<oplus> Some b"
proof -
  obtain a b where "a ## b" "x = the (Some a \<oplus> Some b)" "a \<in> A" "b \<in> B"
    using add_set_def assms by auto
  then show ?thesis by (metis defined_def is_none_simps(1) option.collapse)
qed

lemma set_add_elem_reci:
  assumes "a \<in> A \<and> b \<in> B \<and> Some x = Some a \<oplus> Some b"
  shows "x \<in> A \<oplus>\<oplus> B"
  by (metis (mono_tags, lifting) CollectI add_set_def assms is_none_code(2) option.sel defined_def)

lemma set_add_asso:
  "(A \<oplus>\<oplus> B) \<oplus>\<oplus> D = A \<oplus>\<oplus> (B \<oplus>\<oplus> D)" (is "?g = ?d")
proof -
  have "?g \<subseteq> ?d"
  proof (rule subsetI)
    fix x assume "x \<in> ?g"
    obtain ab d where "Some x = Some ab \<oplus> Some d" "ab \<in> A \<oplus>\<oplus> B" "d \<in> D"
      using \<open>x \<in> A \<oplus>\<oplus> B \<oplus>\<oplus> D\<close> set_add_elem by blast
    then obtain a b where "Some ab = Some a \<oplus> Some b" "a \<in> A" "b \<in> B"
      using set_add_elem by blast
    then obtain bd where "Some bd = Some b \<oplus> Some d"
      by (metis \<open>Some x = Some ab \<oplus> Some d\<close> asso2 not_Some_eq option.simps(3) plus.simps(1))
    then obtain "a ## bd" "b ## d" "Some x = Some a \<oplus> (Some b \<oplus> Some d)"
      by (metis \<open>Some ab = Some a \<oplus> Some b\<close> \<open>Some x = Some ab \<oplus> Some d\<close> associative defined_def is_none_code(2))
    then have "bd \<in> B \<oplus>\<oplus> D"
      using \<open>Some bd = Some b \<oplus> Some d\<close> \<open>b \<in> B\<close> \<open>d \<in> D\<close> set_add_elem_reci by blast
    then show "x \<in> ?d"
      using \<open>Some bd = Some b \<oplus> Some d\<close> \<open>Some x = Some a \<oplus> (Some b \<oplus> Some d)\<close> \<open>a \<in> A\<close> set_add_elem_reci by metis
  qed
  moreover have "?d \<subseteq> ?g"
  proof (rule subsetI)
    fix x assume "x \<in> ?d"
    obtain bd a where "Some x = Some a \<oplus> Some bd" "a \<in> A" "bd \<in> B \<oplus>\<oplus> D"
      using \<open>x \<in> A \<oplus>\<oplus> (B \<oplus>\<oplus> D)\<close> set_add_elem by blast
    then obtain b d where "Some bd = Some b \<oplus> Some d" "d \<in> D" "b \<in> B"
      using set_add_elem by blast
    then obtain ab where "Some ab = Some a \<oplus> Some b"
      by (metis \<open>Some x = Some a \<oplus> Some bd\<close> asso3 not_None_eq plus.simps(1))
    then obtain "ab ## d" "a ## b" "Some x = (Some a \<oplus> Some b) \<oplus> Some d"
      by (metis \<open>Some bd = Some b \<oplus> Some d\<close> \<open>Some x = Some a \<oplus> Some bd\<close> associative defined_def is_none_code(2))
    then have "ab \<in> A \<oplus>\<oplus> B"
      using \<open>Some ab = Some a \<oplus> Some b\<close> \<open>b \<in> B\<close> \<open>a \<in> A\<close> set_add_elem_reci by blast
    then show "x \<in> ?g"
      by (metis \<open>Some ab = Some a \<oplus> Some b\<close> \<open>\<And>thesis. (\<lbrakk>ab ## d; a ## b; Some x = Some a \<oplus> Some b \<oplus> Some d\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>d \<in> D\<close> set_add_elem_reci)
  qed
  ultimately show ?thesis by blast
qed

lemma bigger_set_union:
  assumes "A' >> A"
      and "B' >> B"
    shows "A' \<union> B' >> A \<union> B"
proof -
  have "\<And>x. x \<in> A' \<union> B' \<Longrightarrow> (\<exists>y \<in> A \<union> B. y << x)"
    using assms(1) assms(2) bigger_set_def by auto
  then show ?thesis by (simp add: bigger_set_def)
qed

lemma c_trans_ineq:
  assumes "b << a"
      and "Some a = s_C x \<oplus> Some aa"
      and "Some b = s_C x \<oplus> Some bb"
    shows "bb << aa"
proof -
  obtain c where "Some a = Some b \<oplus> Some c" using assms(1) smaller_def by blast
  then have "s_C x \<oplus> (Some bb \<oplus> Some c) = s_C x \<oplus> Some aa" using assms(2) assms(3) associative by simp
  then have "Some bb \<oplus> Some c = Some aa"
    by (metis assms(2) not_None_eq partially_cancellative plus.simps(3) s_C_def)
  then show ?thesis by (metis smaller_def)
qed

lemma bigger_set_forall:
  "A >> B \<longleftrightarrow> (\<forall>a\<in>A. {a} >> B)"
  by (simp add: bigger_set_def)

lemma subset_smaller:
  assumes "A \<subseteq> B"
  shows "A >> B"
  by (meson assms bigger_set_def in_mono smaller_refl)

lemma bigger_set_trans:
  assumes "A >> B"
      and "B >> D"
    shows "A >> D"
proof -
  have "\<And>a. a \<in> A \<Longrightarrow> (\<exists>d\<in>D. d << a)"
  proof -
    fix a assume "a \<in> A"
    then obtain b where "b \<in> B" "b << a" using assms(1) bigger_set_def by auto
    then obtain d where "d \<in> D" "d << b" using assms(2) bigger_set_def by auto
    then show "\<exists>d\<in>D. d << a" using \<open>b << a\<close> smaller_trans by blast
  qed
  then show ?thesis by (simp add: bigger_set_def)
qed

lemma pure_set_add_smaller:
  assumes "A \<oplus>\<oplus> B = A"
  shows "A >> B"
  by (metis assms rel_bigger_add_set simple_set_add_comm)

lemma decompose_set:
  assumes "x \<in> A \<oplus>\<oplus> B \<oplus>\<oplus> {c} \<oplus>\<oplus> {d}"
  shows "\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some x = Some a \<oplus> Some b \<oplus> Some c \<oplus> Some d"
  by (smt assms elem_add_set singletonD)

lemma add_pure_singleton:
  assumes "A >> B"
      and "A >> {p}"
      and "pure p"
    shows "A >> B \<oplus>\<oplus> {p}"
proof -
  have "\<And>a. a \<in> A \<Longrightarrow> (\<exists>bp \<in> B \<oplus>\<oplus> {p}. bp << a)"
  proof -
    fix a assume "a \<in> A"
    then obtain b where "b \<in> B" "b << a" "p << a" using assms(1) assms(2) bigger_set_def by auto
    then obtain bp where "Some bp = Some b \<oplus> Some p"
      by (metis assms(3) asso3 commutative not_Some_eq plus.simps(1) pure_smaller_ok smaller_def)
    then have "bp << a" using \<open>b << a\<close> \<open>p << a\<close> add_trans assms(3) pure_smaller_ok smaller_refl by blast
    moreover have "bp \<in> B \<oplus>\<oplus> {p}"
      by (meson \<open>Some bp = Some b \<oplus> Some p\<close> \<open>b \<in> B\<close> sep_algebra.set_add_elem_reci sep_algebra_axioms singletonI)
    ultimately show "\<exists>bp \<in> B \<oplus>\<oplus> {p}. bp << a" by blast
  qed
  then show ?thesis by (simp add: bigger_set_def)
qed

lemma add_sets_neutral:
  "A \<oplus>\<oplus> {u} = A" (is "?a = ?b")
proof -
  have "?a \<subseteq> ?b" by (metis option.sel orig_neutral plus.simps(1) set_add_elem singletonD subsetI)
  moreover have "?b \<subseteq> ?a"
    by (metis commutative_monoid.neutral commutative_monoid_axioms set_add_elem_reci singletonI subsetI)
  ultimately show ?thesis by simp
qed

lemma pure_reducibility:
  assumes "pure p"
      and "p << a"
      and "Some a = Some b \<oplus> Some c"
    shows "\<exists>a'. Some a' = s_core b \<oplus> s_core c \<and> p << a'"
proof -
  obtain a' where "Some a' = s_core b \<oplus> s_core c"
    by (metis assms(3) associative commutative decompo_new_plus option.discI option.exhaust_sel plus.simps(2))
  then have "\<sigma> p \<subseteq> \<sigma> a'"
  proof -
    have "\<sigma> a = \<sigma> b \<union> \<sigma> c" 
      by (simp add: assms(3) store_add)
    then have "\<sigma> p \<subseteq> \<sigma> b \<union> \<sigma> c" 
      by (metis assms(1) assms(2) pure_smaller_ok store_add sep_algebra_axioms sup.orderI)
    then show ?thesis 
      by (metis (full_types) \<open>Some a' = s_core b \<oplus> s_core c\<close> s_core_def sep_algebra.store_add sep_algebra_axioms store_pure)
  qed
  then show ?thesis 
    using \<open>Some a' = s_core b \<oplus> s_core c\<close> assms(1) assms(2) assms(3) associative commutative compatible_stores core_properties(1) decompo defined_trans_plus definedness(3) pure_def pure_smaller_ok s_core_def
    by metis
qed

lemma core_add:
  assumes "Some a = Some b \<oplus> Some c"
  shows "s_core a = s_core b \<oplus> s_core c"
proof -
  obtain core_bc where "Some core_bc = s_core b \<oplus> s_core c"
    by (meson assms neutral pure_def pure_reducibility sep_algebra_axioms u_smaller)
  have "core_bc \<in> pure_set a"
  proof -
    obtain "pure |b|" "pure |c|" using core_is_max pure_set_def by auto
    then have "pure core_bc"
      by (metis \<open>Some core_bc = s_core b \<oplus> s_core c\<close> s_core_def sum_pure)
    moreover have "core_bc << a"
      by (smt \<open>Some core_bc = s_core b \<oplus> s_core c\<close> \<open>pure |b|\<close> \<open>pure |c|\<close> assms associative commutative decompo pure_def s_core_def smaller_def)
    ultimately show ?thesis by (simp add: pure_set_def)
  qed
  then have "core_bc << |a|" using core_is_max_uni by blast
  moreover have "|a| << core_bc"
  proof -
    obtain a' where "Some a' = s_core b \<oplus> s_core c" "|a| << a'"
      using pure_reducibility[of "|a|" a b c]
      using assms core_is_max_uni commutative_monoid.pure_set_def commutative_monoid_axioms by fastforce
    then show ?thesis
      by (metis \<open>Some core_bc = s_core b \<oplus> s_core c\<close> option.inject)
  qed
  ultimately show ?thesis
    using \<open>Some core_bc = s_core b \<oplus> s_core c\<close> \<open>core_bc \<in> pure_set a\<close> core_is_max_uni orig_comm pure_set_def pure_smaller_ok s_core_def by fastforce
qed

lemma reduce_add:
  assumes "a ## b"
      and "Some a \<oplus> Some b = Some a \<oplus> Some c"
    shows "s_core a \<oplus> Some b = s_core a \<oplus> Some c"
proof -
  have dac: "a ## c" using assms(1) assms(2) defined_def by auto
  have "s_core a \<oplus> Some b = s_C b \<oplus> s_core (the (Some a \<oplus> Some b))"
    by (smt Option.is_none_def assms(2) associative commutative core_add dac decompo_new_plus defined_def option.collapse)
  moreover have "s_core a \<oplus> Some c = s_C c \<oplus> s_core (the (Some a \<oplus> Some c))"
    by (smt Option.is_none_def associative commutative core_add dac decompo_new_plus defined_def option.collapse)
  moreover have "s_C a \<oplus> s_C b \<oplus> s_core (the (Some a \<oplus> Some b)) = s_C a \<oplus> s_C c \<oplus> s_core (the (Some a \<oplus> Some c))"
    by (metis assms(2) associative calculation(1) calculation(2) commutative decompo_new_plus)
  moreover obtain rb where "Some rb = s_C b \<oplus> s_core (the (Some a \<oplus> Some b))"
    by (metis Option.is_none_def assms(1) calculation(1) defined_def definedness(2) option.collapse s_C_def s_core_def)
  moreover obtain rc where "Some rc = s_C c \<oplus> s_core (the (Some a \<oplus> Some c))"
    by (metis Option.is_none_def dac calculation(2) defined_def definedness(2) option.collapse s_C_def s_core_def)
  ultimately show ?thesis by (metis associative partially_cancellative s_C_def)
qed

lemma c_add:
  assumes "Some a = Some b \<oplus> Some c"
  shows "s_C a = s_C b \<oplus> s_C c"
proof -
  have "Some a = s_core b \<oplus> s_core c \<oplus> s_C b \<oplus> s_C c"
    using assms associative commutative decompo_new_plus by auto
  also have "... = s_core a \<oplus> s_C b \<oplus> s_C c" by (simp add: assms core_add)
  obtain bc where "Some bc = s_C b \<oplus> s_C c"
    by (metis associative calculation plus.elims)
  then have "core bc = u"
    by (metis c_empty_core core_add neutral option.inject s_C_def s_core_def)
  then show ?thesis
    by (metis \<open>Some bc = s_C b \<oplus> s_C c\<close> \<open>s_core b \<oplus> s_core c \<oplus> s_C b \<oplus> s_C c = s_core a \<oplus> s_C b \<oplus> s_C c\<close> associative calculation s_C_def s_core_def unique_c)
qed

lemma pure_c:
  "pure \<phi> \<longleftrightarrow> C \<phi> = u"
  by (metis core_inv core_properties(3) neutral neutral_parts(1) properties_c(1) unique_c)

lemma smaller_pure:
  assumes "a << b"
      and "pure b"
    shows "pure a"
proof -
  obtain c where "Some b = Some a \<oplus> Some c" using assms(1) smaller_def by blast
  moreover have "C b = u"
    by (metis assms(2) core_properties(3) neutral pure_u sep_algebra.unique_c sep_algebra_axioms)
  ultimately have "Some (C a) \<oplus> Some (C c) = Some u"
    using c_add s_C_def by auto
  then have "C a = u" by (metis positivity)
  then show ?thesis by (simp add: pure_c)
qed

lemma antisym:
  assumes "a << b"
      and "b << a"
    shows "a = b"
proof -
  obtain d e where "Some a = Some b \<oplus> Some d" and "Some b = Some a \<oplus> Some e"
    using assms(1) assms(2) smaller_def by blast
  then have "Some a = Some a \<oplus> Some d \<oplus> Some e"
    by (metis associative commutative)
  then have "Some a \<oplus> Some u = Some a \<oplus> (Some d \<oplus> Some e)"
    by (metis associative neutral)
  moreover have "a ## u"
    by (simp add: defined_def orig_neutral)
  ultimately have "s_core a = s_core a \<oplus> (Some d \<oplus> Some e)"
    using reduce_add[of a u "the (Some d \<oplus> Some e)"] defined_trans_plus
    \<open>Some a = Some a \<oplus> Some d \<oplus> Some e\<close> defined_def is_none_simps(1) option.collapse
    by (metis associative neutral)
  obtain de where "Some de = Some d \<oplus> Some e"
    by (metis Option.is_none_def \<open>Some a = Some a \<oplus> Some d \<oplus> Some e\<close> defined_def option.discI option.expand option.sel sep_algebra.defined_trans_plus sep_algebra_axioms)
  then have "de << core a"
    by (metis \<open>s_core a = s_core a \<oplus> (Some d \<oplus> Some e)\<close> commutative s_core_def smaller_def)
  then have "pure de" using core_properties(1) smaller_pure by blast
  then have "pure e" 
    by (metis \<open>Some de = Some d \<oplus> Some e\<close> commutative smaller_def smaller_pure)
  then show ?thesis
    by (metis \<open>Some a = Some a \<oplus> Some d \<oplus> Some e\<close> \<open>Some b = Some a \<oplus> Some e\<close> option.inject commutative_monoid.associative commutative_monoid_axioms pure_def)
qed


lemma smaller_core_comp:
  "b << a \<longleftrightarrow> |b| << |a| \<and> C b << C a" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<Longrightarrow> ?b"
  proof -
    assume "?a"
    obtain c where "Some a = Some b \<oplus> Some c" using \<open>b << a\<close> smaller_def by blast
    then obtain "s_C a = s_C b \<oplus> s_C c" and "s_core a = s_core b \<oplus> s_core c" using c_add core_add by blast
    then show "?b" using s_C_def s_core_def smaller_def by auto
  qed
  moreover have "?b \<Longrightarrow> ?a"
  proof -
    assume "?b"
    obtain "Some a = s_core a \<oplus> s_C a" and "Some b = s_core b \<oplus> s_C b" using decompo_new_plus by blast
    then show "?a" using \<open>|b| << |a| \<and> C b << C a\<close> add_trans decompo by blast
  qed
  ultimately show ?thesis by blast
qed

lemma frame_trans:
  assumes "b << a"
      and "Some a = Some i \<oplus> Some ra"
      and "Some b = Some i \<oplus> Some rb"
      and "Some c = s_core i \<oplus> Some ra"
    shows "rb << c"
proof -
  have "C rb << C ra"
  proof -
    obtain "s_C a = s_C i \<oplus> s_C ra" "s_C b = s_C i \<oplus> s_C rb" using assms(2) c_add assms(3) by blast
    moreover have "C b << C a" using assms(1) c_add s_C_def smaller_def by auto
    ultimately show ?thesis using c_trans_ineq s_C_def by auto
  qed
  moreover have "|rb| << |c|"
  proof -
    have "s_core b = s_core i \<oplus> s_core rb" using assms(3) core_add by blast
    moreover have "|c| = |a|"
      by (smt assms(2) assms(4) core_add core_properties(1) core_properties(3) option.inject commutative_monoid.s_core_def commutative_monoid_axioms)
    ultimately show ?thesis by (metis assms(1) assms(3) commutative smaller_core_comp smaller_def smaller_trans)
  qed
  moreover have "C ra = C c" by (smt assms(4) c_add option.inject orig_neutral commutative_monoid.commutative
        commutative_monoid.plus.simps(1) commutative_monoid.s_core_def commutative_monoid_axioms pure_c s_C_def sep_algebra.core_properties(1) sep_algebra_axioms)
  ultimately obtain "C rb << C c" and "|rb| << |c|" by simp
  then show ?thesis using smaller_core_comp by blast
qed

end

end