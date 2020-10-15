theory Soundness
  imports Semantics
begin

context semantics_algebra
begin

definition wfm :: "('a, 'b, 'c) program \<Rightarrow> 'a assertion \<Rightarrow> bool" where
  "wfm Pr b \<longleftrightarrow> (\<forall>D. smono Pr D (Assume b) \<and> smono Pr D (Assume (lnot b)))"

lemma wfm_not_same:
  "lnot (lnot b) = b"
proof (rule ext)
  fix x 
  show "lnot (lnot b) x = b x" by (simp add: lnot_def)
qed

lemma wfm_not:
  "wfm Pr b \<longleftrightarrow> wfm Pr (lnot b)"
  by (metis wfm_def wfm_not_same)

lemma exhale_false_single:
  "\<not> (ver Pr {\<phi>} (Exhale lfalse))"
  by (simp add: lfalse_def ver_exhale)

fun inlinable :: "('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "inlinable (MethodCall _ _ _) = True"
| "inlinable (While _ _ _) = True"
| "inlinable (Seq a b) = (inlinable a \<or> inlinable b)"
| "inlinable (If a b) = (inlinable a \<or> inlinable b)"
| "inlinable _ = False"

fun inline :: "('a, 'b, 'c) program \<Rightarrow> nat => 'b list \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> ('a, 'b, 'c) stmt" where
  "inline Pr 0 _ (MethodCall _ _ _) = Assume lfalse"
| "inline Pr 0 _ (While b _ _) = Assume (lnot b)"
| "inline Pr (Suc n) l (MethodCall y name x) = (let r = get_method Pr name in
    if r = None then
      (Exhale lfalse)
    else
      let (m, args, ret, P, Q, s) = the r in
      let new_s = rename s (args @ ret, x @ y, l, modif s) in
      let new_l = l @ modif new_s in
      inline Pr n new_l new_s)"
| "inline Pr (Suc n) l (While b I s) = If (Assume b ; inline Pr n l s ; inline Pr n (l @ read (inline Pr n l s)) (While b I s)) (Assume (lnot b))"
| "inline Pr n l (Seq a b) = (let inla = inline Pr n l a in Seq inla (inline Pr n (l @ read inla) b))"
| "inline Pr n l (If a b) = If (inline Pr n l a) (inline Pr n l b)"
| "inline Pr _ _ s = s"

lemma not_inlinable_id:
  "\<not> inlinable s \<Longrightarrow> inline Pr n l s = s"
  apply (induction rule: inline.induct) by auto

lemma empty_set_goes_empty:
  assumes "sem Pr A s1 = {}"
      and "ver Pr A s1"
    shows "sem Pr A (s1 ; s2) = {}"
proof (cases "ver Pr A (s1 ; s2)")
  case True
  then show ?thesis
    using assms(1) sem_seq by auto
next
  case False
  then show ?thesis
    using assms(1) assms(2) ver_def by auto
qed

lemma semantics_union:
  "(\<Union>a\<in>A. sem Pr (f a) s) = sem Pr (\<Union>a\<in>A. f a) s"
  by auto

lemma rename_set_union:
  "(\<Union>a\<in>A. rename_set (f a) t) = rename_set (\<Union>a\<in>A. f a) t"
  by auto

lemma dummy_lemma:
  assumes "Some (m, args, rets, P, Q, s) = get_method Pr m"
  shows "the (get_method Pr m) = (m, args, rets, P, Q, s)"
  by (metis assms option.sel)

definition fill_set :: "'a set \<Rightarrow> 'a set" where
  "fill_set A = {\<phi> |\<phi> \<phi>'. \<phi>' \<in> A \<and> \<phi> << \<phi>'}"

lemma elem_fill_set:
  "\<phi> \<in> fill_set A \<longleftrightarrow> (\<exists>\<phi>' \<in> A. \<phi> << \<phi>')" 
  using fill_set_def by auto

definition sem_ver :: "('a, 'b, 'c) program \<Rightarrow> 'a set \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> 'a set" where
  "sem_ver Pr A s = sem Pr (Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} s) A) s"

definition f :: "'a set \<Rightarrow> 'a assertion \<Rightarrow> 'a set" where
  "f A b = Set.filter (\<lambda>x. b x = Some True) A"

fun 
  SC :: "('a, 'b, 'c) program \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'b list \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" and
  inlinable_SC :: "('a, 'b, 'c) program \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'b list \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool"
where
  "SC Pr n A l st = (if (\<not> inlinable st) then smono Pr A st else inlinable_SC Pr n A l st)"
| "inlinable_SC Pr (Suc n) A l (MethodCall y m x) = (
  if get_method Pr m = None then False
  else
    let (m, args, ret, P, Q, s) = the (get_method Pr m) in
    let new_s = rename s (args @ ret, x @ y, l, modif s) in let new_l = l @ modif new_s in
    framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s)"
| "inlinable_SC Pr (Suc n) A l (While b I s) \<longleftrightarrow> wfm Pr b \<and> framing Pr (f A b) (inline Pr n l s) \<and>
  SC Pr n (f A b) l s \<and> SC Pr n (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) (While b I s)"
| "inlinable_SC Pr n A l (Seq a b) = (let inla = inline Pr n l a in
  SC Pr n A l a \<and> SC Pr n (sem_ver Pr (fill_set A) inla) (l @ read inla) b)"
| "inlinable_SC Pr n A l (If a b) = (SC Pr n A l a \<and> SC Pr n A l b)"
| "inlinable_SC Pr 0 A l (While b _ _) \<longleftrightarrow> smono Pr A (Assume (lnot b))"
| "inlinable_SC Pr 0 A _ _ = True"
| "inlinable_SC Pr _ _ _ _ = undefined"

lemma sc_method_equiv:
  assumes "Some (m, args, rets, P, Q, s) = get_method Pr m"
      and "new_s = rename s (args @ rets, x @ y, l, modif s)"
      and "new_l = l @ modif new_s"
    shows "SC Pr (Suc n) A l (MethodCall y m x) \<longleftrightarrow> framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<longleftrightarrow> inlinable_SC Pr (Suc n) A l (MethodCall y m x)" by simp
  also have "... \<longleftrightarrow>
(if get_method Pr m = None then False
  else
    let (m, args, rets, P, Q, s) = the (get_method Pr m) in
    let new_s = rename s (args @ rets, x @ y, l, modif s) in let new_l = l @ modif new_s in
    framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s)"
    using inlinable_SC.simps(1)[of Pr n A l y m x] by blast
  also have "... \<longleftrightarrow> (let (m, args, rets, P, Q, s) = the (get_method Pr m) in
    let new_s = rename s (args @ rets, x @ y, l, modif s) in let new_l = l @ modif new_s in
    framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s)"
    by (smt assms(1) calculation inlinable_SC.simps(4) not_None_eq)
  also have "... \<longleftrightarrow> (let new_s = rename s (args @ rets, x @ y, l, modif s) in let new_l = l @ modif new_s in
    framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s)"
    using assms option.sel
  proof -
    have "(m, args, rets, P, Q, s) = the (get_method Pr m)"
      using assms(1) dummy_lemma by fastforce
    then show ?thesis by auto
  qed
  also have "... \<longleftrightarrow> ?b"
    by (metis assms(2) assms(3))
  finally show ?thesis by blast
qed

lemma sc_method_implies_not_none:
  assumes "SC Pr (Suc n) A l (MethodCall y m x)"
  shows "get_method Pr m \<noteq> None"
proof (rule ccontr)
  have "inlinable_SC Pr (Suc n) A l (MethodCall y m x)"
    using assms by auto
  assume "\<not> get_method Pr m \<noteq> None"
  then have "get_method Pr m = None" by blast
  moreover have "(let r = get_method Pr m in
  if r = None then False
  else
    let (_, args, ret, _, _, s) = the r in
    let new_s = rename s (args @ ret, x @ y, l, modif s) in let new_l = l @ modif new_s in
    framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s)
\<longleftrightarrow> inlinable_SC Pr (Suc n) A l (MethodCall y m x)"
    by simp
  then show "False" by (smt \<open>inlinable_SC Pr (Suc n) A l (MethodCall y m x)\<close> calculation) 
qed

lemma inlinable_same:
  "inlinable s \<longleftrightarrow> inlinable (rename s t)"
  by (induction s rule: inlinable.induct) simp_all

lemma not_inlinable_sc:
  assumes "\<not> inlinable s"
      and "SC Pr n A l s"
      and "wf_renaming t"
      and "wf_program Pr"
      and "wf_stmt Pr s"
    shows "SC Pr n (rename_set A t) l (rename s t)"
proof -
  have "\<not> inlinable (rename s t)" using assms(1) inlinable_same by auto
  moreover have "mono Pr A s"
    using assms mono_smono by simp
  then have "mono Pr (rename_set A t) (rename s t)" 
    using assms mono_renamed mono_smono
    by blast
  then show ?thesis by (simp add: calculation mono_smono)
qed

lemma wf_renaming_same_order:
  assumes "a << b"
      and "wf_renaming t"
    shows "rename_state a t << rename_state b t"
  by (simp add: assms(1) assms(2) wf_renaming_order)

lemma ver_assume:
  "ver Pr {a} (Assume b) \<longleftrightarrow> b a \<noteq> None" (is "?a \<longleftrightarrow> ?b")
proof -
  have "?a \<longleftrightarrow> well_defined_assert b a" using ver_def semantics.simps(2) by simp
  then show ?thesis 
    by (simp add: well_defined_assert_def)
qed

lemma assume_rename:
  assumes "wf_renaming t"
      and "ver Pr {a} (Assume (rename_pred b t))"
  shows "sem Pr {a} (Assume (rename_pred b t)) = rename_set (sem Pr {rename_state a (rename_inv t)} (Assume b)) t"
proof -
  let ?t = "rename_inv t"
  let ?a = "rename_state a ?t"
  let ?b = "rename_pred b t"
  show ?thesis
  proof (cases "b ?a = Some True")
    case True
    then show ?thesis 
      by (metis assms(1) option.discI rename_singleton sem_assume_true verif_rename_pred well_defined_assert_def wf_rename_inv_other)
  next
    case False
    then have "b ?a = Some False"
    proof -
      have "b ?a \<noteq> None" using assms(2) 
        by (simp add: rename_pred_def ver_assume)
      then show ?thesis 
        using False by auto
    qed
    then show ?thesis 
      by (metis assms(1) ex_in_conv member_rename_set_inv rename_pred_def sem_assume_false)
  qed
qed

lemma wfm_same:
  assumes "wfm Pr b"
      and "wf_renaming t"
      and "wf_program Pr"
      and "wf_stmt Pr s"
    shows "wfm Pr (rename_pred b t)"
proof -
  let ?t = "rename_inv t"
  let ?b = "rename_pred b t"
  have "\<And>A. mono Pr A (Assume ?b) \<and> mono Pr A (Assume (lnot ?b))"
  proof -
    fix A
    have "mono Pr A (Assume ?b)"
    proof (rule monoI)
      fix a ba assume asm: "ba << a \<and> ver Pr {ba} (Assume (rename_pred b t)) \<and> (\<exists>x\<in>A. a << x)"
      then have "rename_pred b t a = b (rename_state a ?t)" 
        by (simp add: rename_pred_def)
      moreover have asm2: "rename_pred b t ba = b (rename_state ba ?t)"  
        using rename_pred_def by auto
      moreover have "rename_state ba ?t << rename_state a ?t" 
        using \<open>ba << a \<and> ver Pr {ba} (Assume (rename_pred b t)) \<and> (\<exists>x\<in>A. a << x)\<close> assms(2) renaming_invert_wf wf_renaming_order by blast
      moreover have "mono Pr ({rename_state a ?t}) (Assume b)" 
        using assms(1) mono_smono wfm_def by blast
      moreover have "ver Pr {rename_state ba ?t} (Assume b)" 
        using asm asm2 ver_assume by auto
      ultimately have "ver Pr {rename_state a ?t} (Assume b) \<and> sem Pr {rename_state a ?t} (Assume b) >> sem Pr {rename_state ba ?t} (Assume b)"
        using mono_smono smaller_refl smonoOut_singleton smono_def ssafeMono_singleton by auto
      then have "ver Pr {a} (Assume (rename_pred b t))"
        using \<open>rename_pred b t a = b (rename_state a (rename_inv t))\<close> ver_assume by auto
      moreover have "sem Pr {a} (Assume (rename_pred b t)) >> sem Pr {ba} (Assume (rename_pred b t))"
        by (metis \<open>ver Pr {rename_state a (rename_inv t)} (Assume b) \<and> sem Pr {rename_state a (rename_inv t)} (Assume b) >> sem Pr {rename_state ba (rename_inv t)} (Assume b)\<close> asm assms(2) assume_rename calculation rename_set_smaller)
      ultimately show "ver Pr {a} (Assume (rename_pred b t)) \<and> sem Pr {a} (Assume (rename_pred b t)) >> sem Pr {ba} (Assume (rename_pred b t))"
        by blast
    qed
    moreover have "mono Pr A (Assume (lnot ?b))"
    proof (rule monoI)
      fix a ba assume asm: "ba << a \<and> ver Pr {ba} (Assume (lnot (rename_pred b t))) \<and> (\<exists>x\<in>A. a << x)"
      then have "lnot (rename_pred b t) a = lnot b (rename_state a ?t)" 
        by (metis rename_pred_def rename_pred_lnot)
      moreover have asm2: "lnot (rename_pred b t) ba = lnot b (rename_state ba ?t)"  
        by (metis rename_pred_def rename_pred_lnot)
      moreover have "rename_state ba ?t << rename_state a ?t"
        using asm assms(2) renaming_invert_wf wf_renaming_order by blast
      moreover have "mono Pr ({rename_state a ?t}) (Assume (lnot b))" 
        using assms(1) mono_smono wfm_def by blast
      moreover have "ver Pr {rename_state ba ?t} (Assume (lnot b))" 
        using asm asm2 ver_assume by auto
      ultimately have "ver Pr {rename_state a ?t} (Assume (lnot b)) \<and> sem Pr {rename_state a ?t} (Assume (lnot b)) >> sem Pr {rename_state ba ?t} (Assume (lnot b))"
        using mono_smono smaller_refl smonoOut_singleton smono_def ssafeMono_singleton by auto
      then have "ver Pr {a} (Assume (lnot (rename_pred b t)))"
        by (simp add: \<open>lnot (rename_pred b t) a = lnot b (rename_state a (rename_inv t))\<close> ver_assume)
      moreover have "sem Pr {a} (Assume (lnot (rename_pred b t))) >> sem Pr {ba} (Assume (lnot (rename_pred b t)))"
        by (metis \<open>ver Pr {rename_state a (rename_inv t)} (Assume (lnot b)) \<and> sem Pr {rename_state a (rename_inv t)} (Assume (lnot b)) >> sem Pr {rename_state ba (rename_inv t)} (Assume (lnot b))\<close> asm assms(2) assume_rename calculation rename_pred_lnot rename_set_smaller)
      ultimately show "ver Pr {a} (Assume (lnot (rename_pred b t))) \<and> sem Pr {a} (Assume (lnot (rename_pred b t))) >> sem Pr {ba} (Assume (lnot (rename_pred b t)))"
        by blast
    qed
    ultimately show "mono Pr A (Assume ?b) \<and> mono Pr A (Assume (lnot ?b))" by blast
  qed
  then show ?thesis
    by (simp add: mono_smono wfm_def)
qed

lemma sc_method_implies_new:
  assumes "new_s = rename s (args @ ret, x @ y, l, modif s)"
      and "new_l = l @ modif new_s"
      and "SC Pr (Suc n) A l (MethodCall y m x)"
      and "get_method Pr m = Some (m, args, ret, P, Q, s)"
    shows "framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s"
proof -
  from assms(3) have "(let (_, args, ret, _, _, s) = the (get_method Pr m) in
    let new_s = rename s (args @ ret, x @ y, l, modif s) in let new_l = l @ modif new_s in
    framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s)"
    using SC.simps inlinable.simps(1) inlinable_SC.simps(1) by meson
  then have "let new_s = rename s (args @ ret, x @ y, l, modif s) in let new_l = l @ modif new_s in
    framing Pr A (inline Pr n new_l new_s) \<and> SC Pr n A new_l new_s" using assms(4)
    by simp
  then show ?thesis using assms by meson
qed

definition no_inter_single :: "'a \<Rightarrow> 'b list \<Rightarrow> bool" where
  "no_inter_single x l \<longleftrightarrow> \<sigma> x \<subseteq> set l"

definition no_inter :: "'a set \<Rightarrow> 'b list \<Rightarrow> bool" where
  "no_inter A l \<longleftrightarrow> (\<forall>a \<in> A. no_inter_single a l)"

lemma no_inter_I:
  "(\<And>a. a \<in> A \<Longrightarrow> \<sigma> a \<subseteq> set l) \<Longrightarrow> no_inter A l"
  by (simp add: no_inter_def no_inter_single_def)

lemma inter_sum_sets:
  assumes "no_inter A l"
      and "no_inter B l"
    shows "no_inter (A \<oplus>\<oplus> B) l"
  by (metis assms(1) assms(2) no_inter_def no_inter_single_def set_add_elem store_add sup_least)

definition SP :: "('a, 'b, 'c) program \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'b list \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "SP Pr n A l s \<longleftrightarrow>
  (ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr s \<and> SC Pr n A l s \<and> no_inter A l \<and> set (modif s) \<subseteq> set l
  \<longrightarrow> (\<forall>\<phi> \<phi>'. (\<exists>\<phi>'' \<in> A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} s \<longrightarrow> ver Pr {\<phi>'} (inline Pr n l s) \<and> 
  (sem Pr {\<phi>'} (inline Pr n l s) >> sem Pr {\<phi>} s)))"

lemma wf_prog_wf_method:
  assumes "Some (m, args, rets, P, Q, s) = get_method Pr m"
      and "wf_program Pr"
    shows "wf_method Pr (m, args, rets, P, Q, s)"
  using assms(1) assms(2) wf_program_method by presburger

lemma wf_meth_stmt_wf_renaming:
  assumes "wf_stmt Pr (MethodCall y m x)"
      and "wf_method Pr (m, args, rets, P, Q, s)"
      and "get_method Pr m = Some (m, args, rets, P, Q, s)"
    shows "wf_renaming (args @ rets, x @ y, l1, l2)"
proof -
  have "let r = get_method Pr m in
  r \<noteq> None \<and> (let (_, args, ret, _, _, _) = the r in length x = length args
  \<and> length y = length ret \<and> distinct (x @ y))"
    using assms(1) by auto
  then have "length x = length args \<and> length y = length rets \<and> distinct (x @ y)" using assms by simp
  moreover have "distinct (args @ rets)" using assms(2) by simp
  ultimately show ?thesis by simp
qed

lemma wf_stmt_inline:
  "wf_stmt Pr s \<and> wf_program Pr \<longrightarrow> wf_stmt Pr (inline Pr n l s)"
proof (induct rule: inline.induct[of "\<lambda>Pr n l s. wf_stmt Pr s \<and> wf_program Pr \<longrightarrow> wf_stmt Pr (inline Pr n l s)"])
  case (3 Pr n l y m x)
  then show ?case
  proof (cases "get_method Pr m")
    case None
    then show ?thesis by simp
  next
    case (Some a)
    then obtain args rets P Q s where "get_method Pr m = Some (m, args, rets, P, Q, s)"
      by (metis fst_conv get_method_same_name old.prod.exhaust option.distinct(1) option.sel)
    then have "wf_stmt Pr (MethodCall y m x) \<and> wf_program Pr \<Longrightarrow> wf_stmt Pr (inline Pr (Suc n) l (MethodCall y m x))"
    proof -
      assume asm: "wf_stmt Pr (MethodCall y m x) \<and> wf_program Pr"
      then have "wf_method Pr (m, args, rets, P, Q, s)"
        using \<open>get_method Pr m = Some (m, args, rets, P, Q, s)\<close> wf_program.simps wf_program_method_aux by blast
      then have "wf_stmt Pr s"
        by simp
      let ?s = "rename s (args @ rets, x @ y, l, modif s)"
      let ?l = "l @ modif ?s"
      let ?s' = "inline Pr n ?l ?s"
      have "inline Pr (Suc n) l (MethodCall y m x) = ?s'" using inline.simps(3)[of Pr n l y m x]
        \<open>get_method Pr m = Some (m, args, rets, P, Q, s)\<close> 
        by (smt dummy_lemma old.prod.case option.distinct(1))
      moreover have "wf_renaming (args @ rets, x @ y, l, modif s)"
        using \<open>get_method Pr m = Some (m, args, rets, P, Q, s)\<close> asm wf_wf_renaming(1) by blast
      then have "wf_stmt Pr ?s"
        using \<open>wf_stmt Pr s\<close> wf_stmt_wf_renaming by blast
      then have "wf_stmt Pr ?s'" using 3 
        using \<open>get_method Pr m = Some (m, args, rets, P, Q, s)\<close> asm by auto
      then show "wf_stmt Pr (inline Pr (Suc n) l (MethodCall y m x))" 
        using calculation by auto
    qed
    then show ?thesis by blast
  qed
next
  case (5 Pr n l a b)
  then show ?case 
    by (metis inline.simps(5) wf_stmt.simps(1))
qed (simp_all)

lemma SC_inlinable_implies_seq:
  assumes "inlinable (s1 ; s2)"
      and "SC Pr n A l (s1 ; s2)"
    shows "SC Pr n A l s1"
      and "SC Pr n (sem_ver Pr (fill_set A) (inline Pr n l s1)) (l @ read (inline Pr n l s1)) s2"
   apply (meson SC.simps assms(1) assms(2) inlinable_SC.simps(3))
  by (meson SC.elims(2) assms(1) assms(2) inlinable_SC.simps(3))

lemma SP_I:
  "(\<And>\<phi> \<phi>'. ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr s \<and> SC Pr n A l s \<and> no_inter A l \<and> set (modif s) \<subseteq> set l
    \<and> (\<exists>\<phi>'' \<in> A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} s \<Longrightarrow> ver Pr {\<phi>'} (inline Pr n l s) \<and> sem Pr {\<phi>'} (inline Pr n l s) >> sem Pr {\<phi>} s)
  \<Longrightarrow> SP Pr n A l s"
  using SP_def by metis

lemma havoc_int_squared_single:
  assumes "Some a = Some v \<oplus> Some r"
      and "set x \<inter> \<sigma> r = {}"
      and "ver Pr {v} (Havoc x)"
    shows "sem Pr {a} (Havoc x) = sem Pr {v} (Havoc x) \<oplus>\<oplus> {r}" (is "?a = ?b")
proof -
  have "sem Pr {a} (Havoc x) = {h_comp a x} \<oplus>\<oplus> h x"
    using assms(1) assms(3) store_add ver_havoc by auto
  moreover have "{a} = {v} \<oplus>\<oplus> {r}" using assms(1) simple_set_add by auto
  moreover have "Some (h_comp a x) = Some (h_comp v x) \<oplus> Some (h_comp r x)" using assms(1) h_comp_lin by blast
  moreover have "h_comp r x = r" by (simp add: assms(2) h_comp_not_here)
  moreover have "sem Pr {v} (Havoc x) = {h_comp v x} \<oplus>\<oplus> h x"
    using assms(3) sem_havoc by blast
  ultimately show ?thesis by (metis (no_types, lifting) set_add_asso simple_set_add simple_set_add_comm)
qed

lemma havoc_invertible:
  assumes "set V \<subseteq> \<sigma> a"
      and "Some b = Some (h_comp a V) \<oplus> Some hv"
      and "hv \<in> h V"
    shows "\<exists>hv' \<in> h V. Some a = Some (h_comp b V) \<oplus> Some hv'"
proof -
  have "h_comp b V << a"
    by (smt Diff_disjoint assms(2) assms(3) h_comp_def h_comp_h h_comp_lin h_comp_not_here h_comp_smaller h_comp_some_sum h_comp_store neutral)
  then obtain r where "Some a = Some (h_comp b V) \<oplus> Some r"
    using smaller_def by blast
  then have "pure r"
    by (metis assms(2) assms(3) c_add h_comp_only_pure h_pure neutral partially_cancellative pure_c s_C_def)
  then have "set V \<subseteq> \<sigma> r"
    using DiffD2 \<open>Some a = Some (h_comp b V) \<oplus> Some r\<close> assms(1) h_comp_store store_add by auto
  then obtain r' where "r' << r" "\<sigma> r' = set V"
    using all_stores_exist by blast
  then have "Some a = Some (h_comp b V) \<oplus> Some r'"
  proof -
    obtain aa where "Some aa = Some (h_comp b V) \<oplus> Some r'"
      by (metis \<open>Some a = Some (h_comp b V) \<oplus> Some r\<close> \<open>r' << r\<close> asso2 commutative option.collapse option.distinct(1) orig_comm plus.simps(1) smaller_def)
    then have "aa << a"
      using \<open>Some a = Some (h_comp b V) \<oplus> Some r\<close> \<open>r' << r\<close> add_trans smaller_refl by blast
    moreover have "a << aa"
    proof -
      have "\<sigma> a = \<sigma> aa"
        using \<open>Some aa = Some (h_comp b V) \<oplus> Some r'\<close> \<open>\<sigma> r' = set V\<close> assms(1) assms(2) assms(3) h_comp_store h_store store_add by auto
      then have "|a| = |aa|"
        by (metis calculation core_properties(1) pure_is_exactly_store_variant smaller_core_comp store_pure)
      then show ?thesis
      proof -
        have f1: "s_core a = s_core aa"
          using \<open>|a| = |aa|\<close> s_core_def by presburger
        have "s_C a = s_C aa"
          using \<open>Some a = Some (h_comp b V) \<oplus> Some r\<close> \<open>Some aa = Some (h_comp b V) \<oplus> Some r'\<close> \<open>pure r\<close> \<open>r' << r\<close> c_add pure_c s_C_def smaller_pure by force
        then show ?thesis
          using f1 by (metis (full_types) decompo_new_plus orig_neutral commutative_monoid.plus.simps(1) commutative_monoid.smaller_def commutative_monoid_axioms)
      qed
    qed
    ultimately show ?thesis
      using \<open>Some aa = Some (h_comp b V) \<oplus> Some r'\<close> local.antisym by blast
  qed
  moreover have "pure r'"
    using \<open>pure r\<close> \<open>r' << r\<close> smaller_pure by blast
  then have "r' \<in> h V" using h_def[of V]
    using \<open>\<sigma> r' = set V\<close> by blast
  then show ?thesis
    using calculation by blast
qed

lemma decompo_sigma:
  assumes "\<sigma> p = a \<union> b"
      and "a \<inter> b = {}"
      and "pure p"
    shows "\<exists>pa pb. Some p = Some pa \<oplus> Some pb \<and> \<sigma> pa = a \<and> \<sigma> pb = b"
proof -
  obtain pa where "pa << p" "\<sigma> pa = a"
    using all_stores_exist assms(1) by blast
  moreover obtain pb where "pb << p" "\<sigma> pb = b"
    using all_stores_exist assms(1) by blast
  moreover have "\<sigma> pa \<inter> \<sigma> pb = {}"
    by (simp add: assms(2) calculation(2) calculation(4))
  moreover obtain "pure pa" "pure pb"
    using assms(3) calculation(1) calculation(3) smaller_pure by blast
  ultimately obtain pp where "Some pp = Some pa \<oplus> Some pb"
    by (metis Option.is_none_def \<open>\<And>thesis. (\<lbrakk>pure pa; pure pb\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> defined_def defined_disjoint_store option.collapse plus.simps(1))
  then have "pp << p"
    by (metis \<open>pa << p\<close> \<open>pb << p\<close> add_trans assms(3) pure_def)
  moreover have "\<sigma> pp = \<sigma> p"
    by (simp add: \<open>Some pp = Some pa \<oplus> Some pb\<close> \<open>\<sigma> pa = a\<close> \<open>\<sigma> pb = b\<close> assms(1) store_add)
  ultimately show ?thesis
    using \<open>Some pp = Some pa \<oplus> Some pb\<close> \<open>\<sigma> pa = a\<close> \<open>\<sigma> pb = b\<close> assms(3) pure_is_exactly_store_variant by blast
qed

lemma smaller_defined:
  assumes "a << b"
      and "b ## r"
    shows "a ## r"
  by (metis Option.is_none_def assms(1) assms(2) asso3 defined_def definedness(3) plus.simps(1) smaller_def)

lemma pure_defined_sum:
  assumes "Some x = Some xx \<oplus> Some p"
      and "pure p"
      and "xx ## r"
      and "p ## r"
    shows "x ## r"
proof -

  obtain y where "Some y = Some xx \<oplus> Some r"
    by (metis assms(3) defined_def is_none_code(1) option.exhaust)

  let ?r = "\<sigma> r \<inter> \<sigma> p"
  let ?r' = "\<sigma> p - ?r"
  obtain pr pr' where "Some p = Some pr \<oplus> Some pr' \<and> \<sigma> pr = ?r \<and> \<sigma> pr' = ?r'"
    using decompo_sigma[of p ?r ?r'] assms(2) by auto
  then have "pure pr'"
    using assms(2) commutative smaller_def smaller_pure by fastforce
  then obtain pxx po where "Some pr' = Some pxx \<oplus> Some po" "\<sigma> pxx = \<sigma> xx \<inter> \<sigma> pr'" "\<sigma> po = \<sigma> pr' - (\<sigma> xx \<inter> \<sigma> pr')"
    using decompo_sigma[of pr' "\<sigma> xx \<inter> \<sigma> pr'" "\<sigma> pr' - (\<sigma> xx \<inter> \<sigma> pr')"] by auto
  then obtain "\<sigma> pxx \<subseteq> \<sigma> xx" "\<sigma> pr \<subseteq> \<sigma> r"
    by (simp add: \<open>Some p = Some pr \<oplus> Some pr' \<and> \<sigma> pr = \<sigma> r \<inter> \<sigma> p \<and> \<sigma> pr' = \<sigma> p - \<sigma> r \<inter> \<sigma> p\<close>)
  then have "Some r = Some r \<oplus> Some pr"
    by (meson \<open>Some p = Some pr \<oplus> Some pr' \<and> \<sigma> pr = \<sigma> r \<inter> \<sigma> p \<and> \<sigma> pr' = \<sigma> p - \<sigma> r \<inter> \<sigma> p\<close> assms(2) assms(4) compatible_stores commutative_monoid.smaller_def commutative_monoid_axioms pure_smaller_ok smaller_defined smaller_pure)
  moreover have "Some xx = Some xx \<oplus> Some pxx"
  proof -
    have "pxx << pr'"
      using \<open>Some pr' = Some pxx \<oplus> Some po\<close> smaller_def by blast
    moreover have "pr' << p"
      using \<open>Some p = Some pr \<oplus> Some pr' \<and> \<sigma> pr = \<sigma> r \<inter> \<sigma> p \<and> \<sigma> pr' = \<sigma> p - \<sigma> r \<inter> \<sigma> p\<close> commutative smaller_def by auto
    ultimately have "pxx << p"
      using smaller_trans by blast
    then show ?thesis
      by (metis \<open>\<sigma> pxx \<subseteq> \<sigma> xx\<close> assms(1) assms(2) commutative compatible_stores defined_trans_plus pure_smaller_ok smaller_pure)
  qed
  moreover have "\<sigma> po \<inter> \<sigma> y = {}"
  proof -
    have "\<sigma> po = ?r' - (\<sigma> xx \<inter> ?r')"
      by (simp add: \<open>Some p = Some pr \<oplus> Some pr' \<and> \<sigma> pr = \<sigma> r \<inter> \<sigma> p \<and> \<sigma> pr' = \<sigma> p - \<sigma> r \<inter> \<sigma> p\<close> \<open>\<sigma> po = \<sigma> pr' - \<sigma> xx \<inter> \<sigma> pr'\<close>)
    moreover have "\<sigma> y = \<sigma> xx \<union> \<sigma> r"
      by (simp add: \<open>Some y = Some xx \<oplus> Some r\<close> store_add)
    ultimately show ?thesis by blast
  qed
  then have "y ## po"
  proof -
    obtain "po << pr'" "pr' << p"
      by (metis \<open>Some p = Some pr \<oplus> Some pr' \<and> \<sigma> pr = \<sigma> r \<inter> \<sigma> p \<and> \<sigma> pr' = \<sigma> p - \<sigma> r \<inter> \<sigma> p\<close> \<open>Some pr' = Some pxx \<oplus> Some po\<close> commutative smaller_def)
    then show ?thesis
      using \<open>\<sigma> po \<inter> \<sigma> y = {}\<close> assms(2) defined_disjoint_store smaller_pure by auto
  qed
  then obtain rr where "Some rr = Some xx \<oplus> Some r \<oplus> Some po"
    by (metis \<open>Some y = Some xx \<oplus> Some r\<close> defined_def is_none_code(1) option.exhaust)
  moreover have "Some p = Some pxx \<oplus> Some pr \<oplus> Some po"
    by (metis \<open>Some p = Some pr \<oplus> Some pr' \<and> \<sigma> pr = \<sigma> r \<inter> \<sigma> p \<and> \<sigma> pr' = \<sigma> p - \<sigma> r \<inter> \<sigma> p\<close> \<open>Some pr' = Some pxx \<oplus> Some po\<close> associative commutative_monoid.commutative commutative_monoid_axioms)
  ultimately have "Some rr = Some xx \<oplus> Some r \<oplus> Some p"
    by (smt associative commutative)
  then show ?thesis
    by (metis Option.is_none_def assms(1) associative commutative defined_def option.discI)
qed

lemma havoc_int_squared:
  assumes "set x \<inter> \<sigma> r = {}"
      and "ver Pr A (Havoc x)"
      and "\<And>\<phi>. \<phi> \<in> A \<Longrightarrow> set x \<subseteq> \<sigma> \<phi>"
    shows "sem Pr (A \<oplus>\<oplus> {r}) (Havoc x) = sem Pr A (Havoc x) \<oplus>\<oplus> {r}" (is "?a = ?b")
proof -
  let ?s = "Havoc x"
  have "?a \<subseteq> ?b"
  proof (rule subsetI)
    fix xx assume "xx \<in> ?a"
    then obtain ar where "ar \<in> A \<oplus>\<oplus> {r}" "xx \<in> sem Pr {ar} ?s"
      by (metis (no_types, lifting) UN_E s_singleton semantics_algebra_axioms)
    then obtain a where "a \<in> A" "Some ar = Some a \<oplus> Some r" using elem_add_set by auto
    then have "sem Pr {ar} ?s = (sem Pr {a} ?s) \<oplus>\<oplus> {r}"
      using assms(1) assms(2) havoc_int_squared_single v_singleton by blast
    then have "xx \<in> sem Pr {a} ?s \<oplus>\<oplus> {r}" using \<open>xx \<in> sem Pr {ar} ?s\<close> by blast
    moreover have "sem Pr {a} ?s \<subseteq> sem Pr A ?s" using \<open>a \<in> A\<close> 
      using elem_sem by blast
    ultimately show "xx \<in> ?b" using elem_add_set by (smt in_mono)
  qed
  have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix y assume "y \<in> ?b"
    then obtain sa where "sa \<in> sem Pr A ?s" "Some y = Some sa \<oplus> Some r" using elem_add_set by auto
    then obtain a where "a \<in> A" "sa \<in> sem Pr {a} ?s" using s_singleton[of Pr A ?s] by auto
    then obtain hx where "hx \<in> h x" "Some sa = Some (h_comp a x) \<oplus> Some hx"
      by (smt assms(2) elem_add_set sem_havoc singletonD v_singleton)
    then obtain hx' where "hx' \<in> h x" "Some a = Some (h_comp sa x) \<oplus> Some hx'"
      using \<open>a \<in> A\<close> assms(3) havoc_invertible by blast
    then have "a ## r"
    proof -
      have "h_comp sa x ## r"
        by (metis Option.is_none_def \<open>Some y = Some sa \<oplus> Some r\<close> associative commutative defined_def h_comp_sum option.discI plus.simps(3))
      moreover have "hx' ## r"
        using \<open>hx' \<in> h x\<close> assms(1) defined_disjoint_store h_pure h_store by blast
      ultimately show ?thesis
        using \<open>Some a = Some (h_comp sa x) \<oplus> Some hx'\<close> \<open>hx' \<in> h x\<close> h_pure pure_defined_sum by blast
    qed
    then obtain ar where "Some ar = Some a \<oplus> Some r"
      by (metis defined_def is_none_code(1) option.exhaust)
    then have "(sem Pr {a} ?s) \<oplus>\<oplus> {r} = sem Pr {ar} ?s"
      using \<open>a \<in> A\<close> assms(1) assms(2) havoc_int_squared_single v_singleton by blast
    moreover have "{ar} = {a} \<oplus>\<oplus> {r}" using \<open>Some ar = Some a \<oplus> Some r\<close> simple_set_add by auto
    moreover have "sem Pr {a} ?s \<subseteq> sem Pr A ?s" using \<open>a \<in> A\<close> using elem_sem by blast
    moreover have "y \<in> sem Pr {ar} ?s"
      using \<open>Some y = Some sa \<oplus> Some r\<close> \<open>sa \<in> sem Pr {a} ?s\<close> calculation(1) set_add_elem_reci by blast
    ultimately show "y \<in> ?a"
      using \<open>Some ar = Some a \<oplus> Some r\<close> \<open>a \<in> A\<close> elem_sem set_add_elem_reci singletonI by metis
  qed
  then show ?thesis
    using \<open>sem Pr (A \<oplus>\<oplus> {r}) (Havoc x) \<subseteq> sem Pr A (Havoc x) \<oplus>\<oplus> {r}\<close> \<open>sem Pr A (Havoc x) \<oplus>\<oplus> {r} \<subseteq> sem Pr (A \<oplus>\<oplus> {r}) (Havoc x)\<close> by blast
qed

lemma simple_sem_exhale:
  assumes "wf_assert P"
      and "Some \<phi> = Some i \<oplus> Some r"
      and "i \<in> Inh P"
      and "Some \<phi>' = s_core i \<oplus> Some r"
    shows "{\<phi>'} \<subseteq> sem Pr {\<phi>} (Exhale P)" (is "?b \<subseteq> ?a")
proof -
  have verif: "ver Pr {\<phi>} (Exhale P)"
  proof -
    have "ver Pr {i} (Exhale P)"
      using assms(1) assms(3) 
      by (simp add: subset_smaller supported_intui_exhale)
    then show ?thesis
      by (smt add_trans assms(1) assms(2) elem_add_set insertI1 neutral orig_neutral singleton_iff smaller_refl ssafeMono_singleton u_smaller v_singleton wf_assert_monoIn(2))
  qed
  then show "?b \<subseteq> ?a" using assms(1) assms(2) assms(3) assms(4) exhale_elem local.wf_assert_def by blast
qed

lemma h_set_pure:
  assumes "A >> B"
      and "A >> h x"
    shows "A >> B \<oplus>\<oplus> h x"
proof -
  have "\<And>a. a \<in> A \<Longrightarrow> (\<exists>bhx \<in> B \<oplus>\<oplus> h x. bhx << a)"
  proof -
    fix a assume "a \<in> A"
    then obtain b hx where "b \<in> B" "hx \<in> h x" "b << a" "hx << a" by (meson assms(1) assms(2) bigger_set_def)
    then have "Some a = Some a \<oplus> Some hx" using h_pure pure_smaller_ok by blast
    then obtain bhx where "Some bhx = Some b \<oplus> Some hx" 
      by (metis \<open>b << a\<close> asso2 option.exhaust_sel orig_comm plus.simps(1) smaller_def)
    then have "bhx << a"
      using \<open>Some a = Some a \<oplus> Some hx\<close> \<open>b << a\<close> add_trans smaller_refl by blast
    then show "\<exists>bhx \<in> B \<oplus>\<oplus> h x. bhx << a"
      using \<open>Some bhx = Some b \<oplus> Some hx\<close> \<open>b \<in> B\<close> \<open>hx \<in> h x\<close> set_add_elem_reci by blast
  qed
  then show ?thesis by (simp add: bigger_set_def)
qed

lemma bigger_h_single:
  assumes "set x \<subseteq> \<sigma> a"
  shows "{a} >> {h_comp a x} \<oplus>\<oplus> h x"
proof -
  have "Some a = Some (h_comp a x) \<oplus> s_core a" by (simp add: h_comp_sum)
  moreover have "{ |a| } >> h x" using assms h_bigger store_pure by blast
  ultimately show ?thesis
    by (metis plus_and_bigger_set s_core_def simple_set_add simple_set_add_comm)
qed

lemma core_i_phi_exhale:
  assumes "Some i_phi = Some i \<oplus> Some x"
      and "Some core_i_phi = s_core i \<oplus> Some x"
      and "i \<in> Inh P"
      and "wf_assert P"
      and "P i_phi = Some true"
    shows "{core_i_phi} \<subseteq> sem Pr {i_phi} (Exhale P)" (is "?b \<subseteq> ?a")
  using assms(1) assms(2) assms(3) assms(4) simple_sem_exhale by blast

lemma get_method_inlined:
  assumes "get_method Pr m = Some (m, args, ret, P, Q, s)"
      and "new_s = rename s (args @ ret, x @ y, l, modif s)"
      and "new_l = l @ modif new_s"
    shows "inline Pr (Suc n) l (MethodCall y m x) = inline Pr n new_l new_s"
proof -
  have "inline Pr (Suc n) l (MethodCall y m x) =
(     let new_s = rename s (args @ ret, x @ y, l, modif s) in
      let new_l = l @ modif new_s in
      inline Pr n new_l new_s)" using assms by simp
  then show ?thesis using assms by metis
qed

lemma no_inter_inline_general:
  "wf_program Pr \<and> wf_stmt Pr s \<Longrightarrow> set l \<inter> set (modif (inline Pr n l s)) \<subseteq> set (modif s)"
proof (induction Pr n l s rule: inline.induct)
  case (3 Pr n l y m x)

  thm "3.prems"



  then show ?case
  proof (cases "get_method Pr m = None")
    case True
    then have "inline Pr (Suc n) l (MethodCall y m x) = Exhale lfalse" by simp
    then show ?thesis
      using "3.prems" True by auto
  next
    case False
    then obtain args ret P Q s where "Some (m, args, ret, P, Q, s) = get_method Pr m"
      using get_method_same_name by fastforce
    define new_s where "new_s = rename s (args @ ret, x @ y, l, modif s)"
    define new_l where "new_l = l @ modif new_s"
    have "inline Pr (Suc n) l (MethodCall y m x) = inline Pr n new_l new_s"
      by (metis \<open>Some (m, args, ret, P, Q, s) = get_method Pr m\<close> new_l_def new_s_def get_method_inlined semantics_algebra_axioms)
    then have "set (modif new_s) \<inter> set l \<subseteq> set y"
    proof -
      have "wf_method Pr (m, args, ret, P, Q, s)"
        by (metis "3.prems" \<open>Some (m, args, ret, P, Q, s) = get_method Pr m\<close> wf_program_method semantics_algebra_axioms)
      then have "wf_renaming (args @ ret, x @ y, l, l)"
        by (metis "3.prems" \<open>Some (m, args, ret, P, Q, s) = get_method Pr m\<close> wf_wf_renaming(2))

      moreover have "set (modif new_s) \<inter> set l \<subseteq> set (x @ y)"
        using "3.prems" Un_subset_iff \<open>Some (m, args, ret, P, Q, s) = get_method Pr m\<close> inf_sup_distrib1 new_s_def rename_removes_vars_modif semantics_algebra.wf_wf_renaming(1) semantics_algebra_axioms set_eq_subset
        by smt
      then have "set (modif new_s) \<inter> set l \<subseteq> set x \<union> set y"
        by (metis Int_lower2 inf.orderE inf_assoc modif_in_read set_append)
      moreover have "set (modif new_s) \<inter> set x = {}"
      proof -
        have "set (modif s) \<inter> set args = {}"
        proof -
          have "wf_method Pr (m, args, ret, P, Q, s)"
            using \<open>wf_method Pr (m, args, ret, P, Q, s)\<close> by blast
          then show ?thesis
            by (simp add: Int_commute)
        qed
        then show ?thesis using rename_modif_no_inter[of args ret x y l]
          using inf_commute wf_wf_renaming(2) semantics_algebra_axioms wf_wf_renaming(1)
          using "3.prems" \<open>Some (m, args, ret, P, Q, s) = get_method Pr m\<close> new_s_def
          modif_in_read semantics_algebra.wf_method_exists_equiv
          by (metis le_iff_sup sup.idem)
      qed
      show ?thesis
      proof (rule subsetI)
         fix r assume "r \<in> set (modif new_s) \<inter> set l"
         then have "r \<in> set x \<or> r \<in> set y"
           using \<open>set (modif new_s) \<inter> set l \<subseteq> set x \<union> set y\<close> by blast
        then show "r \<in> set y"
          using \<open>r \<in> set (modif new_s) \<inter> set l\<close> \<open>set (modif new_s) \<inter> set x = {}\<close> by auto
      qed
    qed
    moreover have "wf_program Pr \<and> wf_stmt Pr new_s"
      by (metis "3.prems" \<open>Some (m, args, ret, P, Q, s) = get_method Pr m\<close> new_s_def wf_method.simps wf_program_method wf_stmt_wf_renaming wf_wf_renaming(2))
    ultimately have "set new_l \<inter> set (modif (inline Pr n new_l new_s)) \<subseteq> set (modif new_s)"
      using "3.IH"[of "Some (m, args, ret, P, Q, s)" "(m, args, ret, P, Q, s)" m _ args _ ret _ P _ Q s new_s new_l]
      new_l_def new_s_def
      by (metis "3.prems" \<open>Some (m, args, ret, P, Q, s) = get_method Pr m\<close> option.sel option.simps(3))
    then show ?thesis
      using \<open>inline Pr (Suc n) l (MethodCall y m x) = inline Pr n new_l new_s\<close> \<open>set (modif new_s) \<inter> set l \<subseteq> set y\<close> new_l_def by auto
  qed
next
  case (4 Pr n l b I s)
  have "inline Pr (Suc n) l (While b I s) = If (Assume b; inline Pr n l s; inline Pr n (l @ read (inline Pr n l s)) (While b I s)) (Assume (lnot b))"
    by simp
  then have "set (modif (inline Pr (Suc n) l (While b I s))) = set (modif (inline Pr n l s)) \<union> set (modif (inline Pr n (l @ read (inline Pr n l s)) (While b I s)))"
    by simp
  moreover have "set l \<inter> set (modif (inline Pr n l s)) \<subseteq> set (modif s)"
    using "4.IH"(1) "4.prems" by auto
  moreover have "set (l @ read (inline Pr n l s)) \<inter> set (modif (inline Pr n (l @ read (inline Pr n l s)) (While b I s))) \<subseteq> set (modif (While b I s))"
    using "4.IH"(3) "4.prems" by linarith
  ultimately show ?case by auto
next
  case (5 Pr n l a b)
  define ia where "ia = inline Pr n l a"
  then have "modif (inline Pr n l (a ; b)) = modif ia @ modif (inline Pr n (l @ read ia) b)"
    by (metis inline.simps(5) modif.simps(1))

  moreover have "set l \<inter> set (modif ia) \<subseteq> set (modif a)"
    using "5.IH"(1) ia_def "5.prems" by simp

  moreover have "set (l @ read ia) \<inter> set (modif (inline Pr n (l @ read ia) b)) \<subseteq> set (modif b)"
    using "5.IH"(2)[of ia] ia_def "5.prems" wf_stmt.simps(1) by blast
  moreover have "set l \<subseteq> set (l @ read ia)" by auto
  ultimately have "set l \<inter> set (modif (inline Pr n (l @ read ia) b)) \<subseteq> set (modif b)"
    by blast
  moreover have "set (modif (inline Pr n l (a ; b))) = set (modif ia) \<union> set (modif (inline Pr n (l @ read ia) b))"
    using \<open>modif (inline Pr n l (a ; b)) = modif ia @ modif (inline Pr n (l @ read ia) b)\<close> by auto

  ultimately show ?case
    using \<open>set l \<inter> set (modif ia) \<subseteq> set (modif a)\<close> by auto
next
  case (6 Pr n l a b)
  then show ?case using semantics_algebra_axioms by fastforce
qed (simp_all)

lemma ver_program_method_verif_aux:
  "ver_program_aux Pr Pr_bis \<and> Some (m, args, ret, P, Q, s) = get_method Pr_bis m \<Longrightarrow> ver Pr {u} (Var (args @ ret) ; Inhale P ; s ; Exhale Q)"
proof (induction Pr_bis)
  case Nil
  then have "get_method Pr_bis m = None"
    by auto
  then show ?case
    using Nil.prems by auto
next
  case (Cons a Pr_bis)
  then show ?case
  proof (cases "fst a = m")
    case True
    then have "a = (m, args, ret, P, Q, s)"
      using Cons.prems by auto
    then show ?thesis
      using Cons.prems by auto
  next
    case False
    then have "Some (m, args, ret, P, Q, s) = get_method Pr_bis m"
      by (simp add: Cons.prems)
    then show ?thesis
    proof -
      have "\<forall>p ps psa. ver_program_aux psa ps \<or> \<not> ver_program_aux psa (p # ps)"
        by simp
      then show ?thesis
        using Cons.IH Cons.prems \<open>Some (m, args, ret, P, Q, s) = get_method Pr_bis m\<close> by blast
    qed
  qed
qed

lemma ver_program_method_verif:
  assumes "ver_program Pr"
      and "Some (m, args, ret, P, Q, s) = get_method Pr m"
    shows "ver Pr {u} (Var (args @ ret) ; Inhale P ; s ; Exhale Q)"
  using assms(1) assms(2) ver_program.simps ver_program_method_verif_aux by blast

lemma verif_inhale_var_alone:
  assumes "ver Pr {u} (Var (args @ ret) ; Inhale P)"
  shows "sem Pr {u} (Var (args @ ret) ; Inhale P) = h args \<oplus>\<oplus> h ret \<oplus>\<oplus> Inh P"
proof -
  have "sem Pr {u} (Var (args @ ret)) = h args \<oplus>\<oplus> h ret"
    using havoc_concat var_sem_empty by blast
  then show ?thesis
    by (smt assms sem_inhale sem_seq semantics_algebra_axioms ver_inhale ver_seq)
qed

lemma verif_inhale_var:
  assumes "ver Pr {u} (Var (args @ ret) ; Inhale P ; s)"
  shows "sem Pr {u} (Var (args @ ret) ; Inhale P ; s) = sem Pr (h args \<oplus>\<oplus> h ret \<oplus>\<oplus> Inh P) s"
proof -
  have "sem Pr {u} (Var (args @ ret)) = h args \<oplus>\<oplus> h ret"
    using havoc_concat var_sem_empty by blast
  then show ?thesis
    by (smt assms sem_inhale sem_seq semantics_algebra_axioms ver_inhale ver_seq)
qed

lemma ver_asso:
  "ver Pr A (s1 ; (s2 ; s3)) \<longleftrightarrow> ver Pr A ((s1 ; s2) ; s3)"
  using sem_seq ver_seq by auto

lemma sem_asso:
  assumes "ver Pr A (s1 ; s2 ; s3)"
  shows "sem Pr A (s1 ; (s2 ; s3)) = sem Pr A ((s1 ; s2) ; s3)"
  by (smt assms sem_seq ver_seq)

lemma ver_pr_aux_method:
  assumes "Some (m, args, rets, P, Q, s) = get_method Pr m"
      and "ver_program Pr"
    shows "ver Pr {u} (Var (args @ rets) ; Inhale P ; s ; Exhale Q)"
proof -
  have "Some (m, args, rets, P, Q, s) = get_method Pr m \<and> ver_program_aux Pr Pr \<Longrightarrow> ver Pr {u} (Var (args @ rets) ; Inhale P ; s ; Exhale Q)"
    using ver_program_method_verif_aux by blast
  then show ?thesis
    using assms(1) assms(2) ver_program.elims(2) by blast
qed

lemma bigger_sets_sum:
  assumes "A1 >> B1"
      and "A2 >> B2"
    shows "A1 \<oplus>\<oplus> A2 >> B1 \<oplus>\<oplus> B2"
  by (metis assms(1) assms(2) bigger_set_trans plus_and_bigger_set simple_set_add_comm)

lemma inequality_remove_C:
  assumes "C a1 = C a2"
      and "Some x1 = s_C a1 \<oplus> Some b1"
      and "Some x2 = s_C a2 \<oplus> Some b2"
      and "x1 << x2"
    shows "b1 << b2"
  using assms(1) assms(2) assms(3) assms(4) c_trans_ineq s_C_def by auto

lemma s_C_sum_three:
  assumes "Some x = Some x1 \<oplus> Some x2 \<oplus> Some x3"
  shows "s_C x = s_C x1 \<oplus> s_C x2 \<oplus> s_C x3"
  by (metis assms c_add option.distinct(1) option.exhaust plus.simps(1) plus.simps(2))

lemma biggerSingletonI:
  "(\<And>x. x \<in> A \<Longrightarrow> {x} >> B) \<Longrightarrow> A >> B"
  using bigger_set_forall by blast

lemma instantiate_SP:
  assumes "SP Pr n A l s"
      and "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr s \<and> SC Pr n A l s \<and> no_inter A l \<and> set (modif s) \<subseteq> set l"
      and "(\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} s"
    shows "ver Pr {\<phi>'} (inline Pr n l s) \<and> sem Pr {\<phi>'} (inline Pr n l s) >> sem Pr {\<phi>} s"
  using SP_def[of Pr n A l s] assms by blast

lemma instantiate_framing:
  assumes "framing Pr A s"
      and "(\<exists>s a. Some s = Some \<phi> \<oplus> Some r \<and> s << a \<and> a \<in> A)"
      and "ver Pr {\<phi>} s"
      and "set (modif s) \<inter> \<sigma> r = {}"
    shows "sem Pr ({\<phi>} \<oplus>\<oplus> {r}) s >> sem Pr {\<phi>} s \<oplus>\<oplus> {r}"
  using assms(1) assms(2) assms(3) assms(4) framing.simps by blast

subsection \<open>Method case\<close>

lemma method_inlining_induct:
  assumes "SP Pr n A new_l new_s"
      and "Some (m, args, rets, P, Q, s) = get_method Pr m"
      and "new_s = rename s (args @ rets, x @ y, l, modif s)"
      and "new_l = l @ modif new_s"
    shows "SP Pr (Suc n) A l (MethodCall y m x)"
proof (rule SP_I)
  fix \<phi> \<phi>'
  let ?m = "MethodCall y m x"
  assume asm: "ver_program Pr \<and> wf_program Pr \<and>  wf_stmt Pr (MethodCall y m x) \<and> SC Pr (Suc n) A l (MethodCall y m x)
  \<and> no_inter A l \<and> set (modif (MethodCall y m x)) \<subseteq> set l \<and> (\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} (MethodCall y m x)"

  then have ver_meth_empty: "ver Pr {u} (Var (args @ rets) ; Inhale P ; s ; Exhale Q)" using ver_pr_aux_method assms(2)
    by simp

  moreover have wf_meth: "wf_method Pr (m, args, rets, P, Q, s)" using wf_program_method asm
    using assms(2) by presburger
  then have "wf_stmt Pr s"
    using wf_method.simps by blast

  let ?t = "(args @ rets, x @ y, l, modif s)"
  have "wf_renaming ?t"
  proof -
    have "wf_stmt Pr ?m" using asm by simp
    then have "(let r = get_method Pr m in r \<noteq> None \<and> (let (_, args, rets, _, _, _) = the r in length x = length args
  \<and> length y = length rets \<and> distinct (x @ y)))" by simp
    then have "length x = length args \<and> length y = length rets \<and> distinct (x @ y)"
      by (metis \<open>wf_stmt Pr (MethodCall y m x)\<close> assms(2) wf_method_exists_equiv)
    moreover have "distinct (args @ rets)" using wf_meth
      using wf_method.simps by blast
    ultimately show ?thesis
      by simp
  qed
  let ?P = "rename_pred P ?t"
  let ?Q = "rename_pred Q ?t"
  have "?P = rename_pred P (args @ rets, x @ y, [], []) \<and> wf_assert ?P"
  proof -
    have "set (read_pred P) \<subseteq> set args"
      by (metis assms(2) asm wf_program_method wf_method.simps)
    then have "set (read_pred P) \<subseteq> set (args @ rets)"
      by auto
    then have "?P = rename_pred P (args @ rets, x @ y, [], [])"
      by (metis assms(2) asm semantics_algebra.rename_doesnt_change_if_not_affected semantics_algebra.wf_method.simps semantics_algebra.wf_program_method semantics_algebra.wf_wf_renaming(1) semantics_algebra_axioms)
    then show ?thesis
      using \<open>wf_renaming (args @ rets, x @ y, l, modif s)\<close> same_wf_rename wf_meth wf_method.simps by blast
  qed
  moreover have "rename_pred Q (args @ rets, x @ y, [], []) = ?Q \<and> wf_assert ?Q"
  proof -
    have "wf_method Pr (m, args, rets, P, Q, s)"
      using assms(2) asm wf_program_method by presburger
    then have "set (read_pred Q) \<subseteq> set args \<union> set rets"
      using wf_method.simps by blast
    then have "rename_pred Q (args @ rets, x @ y, [], []) = ?Q"
      by (metis assms(2) asm semantics_algebra.rename_doesnt_change_if_not_affected semantics_algebra.wf_method.simps semantics_algebra.wf_program_method semantics_algebra.wf_wf_renaming(1) semantics_algebra_axioms set_append)
    then show ?thesis
      using \<open>wf_renaming (args @ rets, x @ y, l, modif s)\<close> same_wf_rename wf_meth wf_method.simps by blast
  qed

  let ?s = "rename s ?t"

  have "ver Pr {u} (Var (x @ y) ; Inhale ?P ; ?s ; Exhale ?Q)"
  proof -
    have "wf_stmt Pr (Var (args @ rets) ; Inhale P ; s ; Exhale Q)"
    proof -
      have "wf_stmt Pr s"
        using wf_meth wf_method.simps by blast
      moreover obtain "wf_stmt Pr (Inhale P)" "wf_stmt Pr (Exhale Q)"
        using wf_meth by auto
      ultimately show ?thesis by simp
    qed
    then have "ver Pr (rename_set {u} ?t) (rename (Var (args @ rets) ; Inhale P ; s ; Exhale Q) ?t)" using ver_meth_empty
      using rename_ver_set[of Pr "{u}" _ ?t] \<open>wf_renaming (args @ rets, x @ y, l, modif s)\<close> asm by blast
    then show ?thesis
      using \<open>wf_renaming (args @ rets, x @ y, l, modif s)\<close> rename_list_same rename_set_empty by auto
  qed

  then have "ver Pr (h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?P) ?s \<and> sem Pr (h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?P) ?s >> Inh ?Q"
    by (metis (no_types, lifting) \<open>rename_pred Q (args @ rets, x @ y, [], []) = rename_pred Q (args @ rets, x @ y, l, modif s) \<and> wf_assert (rename_pred Q (args @ rets, x @ y, l, modif s))\<close> supported_intui_exhale ver_seq verif_inhale_var verif_inhale_var_alone)

  moreover have "ver Pr {\<phi>} (Exhale ?P ; Havoc y ; Inhale ?Q)"
  proof -
    have "ver Pr {\<phi>} (Exhale (rename_pred P (args @ rets, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ rets, x @ y, [], [])))"
      using asm ver_method_real[of Pr m args rets P Q s \<phi> y x]
      by (simp add: assms(2))
    then show ?thesis
      by (simp add: \<open>rename_pred Q (args @ rets, x @ y, [], []) = rename_pred Q (args @ rets, x @ y, l, modif s) \<and> wf_assert (rename_pred Q (args @ rets, x @ y, l, modif s))\<close> calculation(2))
  qed

  then have "{\<phi>} >> Inh ?P"
    using calculation(2) supported_intui_exhale ver_seq by blast
  then obtain i r where "i \<in> Inh ?P" "Some \<phi> = Some i \<oplus> Some r"
    using bigger_set_def smaller_def by auto
  let ?r = "h_comp r y"
  have "Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some ?r"
    by (smt \<open>Some \<phi> = Some i \<oplus> Some r\<close> associative core_add h_comp_sum commutative_monoid.commutative commutative_monoid.s_core_def commutative_monoid_axioms pure_smaller_ok sep_algebra.core_properties(1) sep_algebra.core_properties(2) sep_algebra_axioms)

  obtain i_phi where "Some i_phi = Some i \<oplus> s_core \<phi>"
    by (metis \<open>Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some (h_comp r y)\<close> option.discI plus.elims)
  then obtain core_i_phi where "Some core_i_phi = s_core i \<oplus> s_core \<phi>"
    by (metis core_add core_properties(3) s_core_def sep_algebra.core_properties(1) sep_algebra_axioms)
  then have "core_i_phi << i_phi"
    by (metis \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> associative decompo commutative_monoid.commutative commutative_monoid.smaller_def commutative_monoid_axioms s_core_def)
  then obtain core_i_phi_r where "Some core_i_phi_r = Some core_i_phi \<oplus> Some ?r"
    by (metis \<open>Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some (h_comp r y)\<close> \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> asso2 not_Some_eq option.distinct(1) orig_comm plus.simps(1) smaller_def)

  have "Some core_i_phi_r = s_core i \<oplus> (s_core \<phi> \<oplus> Some ?r)"
    by (simp add: \<open>Some core_i_phi = s_core i \<oplus> s_core \<phi>\<close> \<open>Some core_i_phi_r = Some core_i_phi \<oplus> Some (h_comp r y)\<close> associative)
  moreover have "Some \<phi> = Some i \<oplus> (s_core \<phi> \<oplus> Some ?r)"
    by (simp add: \<open>Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some (h_comp r y)\<close> associative)

  moreover have "core_i_phi = |\<phi>|"
  proof -
    have "|i| << |\<phi>|" 
      using \<open>Some \<phi> = Some i \<oplus> Some r\<close> smaller_core_comp smaller_def by blast
    then show ?thesis 
      by (metis \<open>Some core_i_phi = s_core i \<oplus> s_core \<phi>\<close> commutative core_properties(1) option.sel pure_smaller_ok s_core_def)
  qed

  moreover have "\<sigma> ?r \<inter> set y = {}"
    by (simp add: h_comp_store inf.commute)

  ultimately have sem_method_call: "{h_comp |\<phi>| y} \<oplus>\<oplus> {?r} \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?Q \<subseteq> sem Pr {\<phi>} ?m"
  proof -
    have "sem Pr {\<phi>} ?m = sem Pr {\<phi>} (Exhale (rename_pred P (args @ rets, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ rets, x @ y, [], [])))"
      using sem_method_real[of Pr m args rets P Q s \<phi> y x]
      using asm assms(2) by simp
    then have "... = sem Pr {\<phi>} (Exhale ?P ; Havoc y ; Inhale ?Q)"
      by (simp add: \<open>rename_pred P (args @ rets, x @ y, l, modif s) = rename_pred P (args @ rets, x @ y, [], []) \<and> wf_assert (rename_pred P (args @ rets, x @ y, l, modif s))\<close> \<open>rename_pred Q (args @ rets, x @ y, [], []) = rename_pred Q (args @ rets, x @ y, l, modif s) \<and> wf_assert (rename_pred Q (args @ rets, x @ y, l, modif s))\<close>)

    then have "{core_i_phi_r} \<subseteq> sem Pr {\<phi>} (Exhale ?P)"
    proof -
      obtain phi_r where "Some phi_r = s_core \<phi> \<oplus> Some ?r"
        by (metis \<open>Some \<phi> = Some i \<oplus> (s_core \<phi> \<oplus> Some (h_comp r y))\<close> plus.elims)
      then have "Some \<phi> = Some i \<oplus> Some phi_r"
        by (simp add: \<open>Some \<phi> = Some i \<oplus> (s_core \<phi> \<oplus> Some (h_comp r y))\<close>)
      then have "{the (s_core i \<oplus> Some phi_r)} \<subseteq> sem Pr {\<phi>} (Exhale (rename_pred P (args @ rets, x @ y, l, modif s)))"
        using \<open>i \<in> Inh (rename_pred P (args @ rets, x @ y, l, modif s))\<close> exhale_sem_inh
        by (metis \<open>Some core_i_phi_r = s_core i \<oplus> (s_core \<phi> \<oplus> Some (h_comp r y))\<close> \<open>Some phi_r = s_core \<phi> \<oplus> Some (h_comp r y)\<close> \<open>rename_pred P (args @ rets, x @ y, l, modif s) = rename_pred P (args @ rets, x @ y, [], []) \<and> wf_assert (rename_pred P (args @ rets, x @ y, l, modif s))\<close> option.sel simple_sem_exhale)
      then show ?thesis
        by (metis \<open>Some core_i_phi_r = s_core i \<oplus> (s_core \<phi> \<oplus> Some (h_comp r y))\<close> \<open>Some phi_r = s_core \<phi> \<oplus> Some (h_comp r y)\<close> option.sel)
    qed

    moreover have "sem Pr {core_i_phi_r} (Havoc y ; Inhale ?Q) = {h_comp |\<phi>| y} \<oplus>\<oplus> {?r} \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?Q"
    proof -
      have "ver Pr {core_i_phi_r} (Havoc y ; Inhale ?Q)"
      proof -
        have "ver Pr (sem Pr {\<phi>} (Exhale ?P)) (Havoc y ; Inhale ?Q)"
          using \<open>ver Pr {\<phi>} (Exhale (rename_pred P (args @ rets, x @ y, l, modif s)) ; Havoc y ; Inhale (rename_pred Q (args @ rets, x @ y, l, modif s)))\<close> ver_asso ver_seq_single by blast
        then show ?thesis
          by (meson calculation insert_subset v_singleton)
      qed
      then have "sem Pr {core_i_phi_r} (Havoc y ; Inhale ?Q) = {h_comp core_i_phi_r y} \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?Q"
        by (metis (full_types) sem_havoc sem_inhale sem_seq_single ver_inhale ver_seq)
      moreover have "Some (h_comp core_i_phi_r y) = Some (h_comp core_i_phi y) \<oplus> Some (h_comp ?r y)"
        using \<open>Some core_i_phi_r = Some core_i_phi \<oplus> Some (h_comp r y)\<close> h_comp_lin by blast
      ultimately have "{h_comp core_i_phi_r y} = {h_comp |\<phi>| y} \<oplus>\<oplus> {?r}"
        using \<open>core_i_phi = |\<phi>|\<close> h_comp_not_here h_comp_store simple_set_add by auto
      then show ?thesis
        using \<open>sem Pr {core_i_phi_r} (Havoc y ; Inhale (rename_pred Q (args @ rets, x @ y, l, modif s))) = {h_comp core_i_phi_r y} \<oplus>\<oplus> h y \<oplus>\<oplus> Inh (rename_pred Q (args @ rets, x @ y, l, modif s))\<close> by auto
    qed

    moreover have "sem Pr {core_i_phi_r} (Havoc y ; Inhale ?Q) \<subseteq> sem Pr {\<phi>} ?m"
    proof -
      have "sem Pr {\<phi>} ?m = sem Pr (sem Pr {\<phi>} (Exhale ?P)) (Havoc y ; Inhale ?Q)"
        using \<open>sem Pr {\<phi>} (Exhale (rename_pred P (args @ rets, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ rets, x @ y, [], []))) = sem Pr {\<phi>} (Exhale (rename_pred P (args @ rets, x @ y, l, modif s)) ; Havoc y ; Inhale (rename_pred Q (args @ rets, x @ y, l, modif s)))\<close> \<open>sem Pr {\<phi>} (MethodCall y m x) = sem Pr {\<phi>} (Exhale (rename_pred P (args @ rets, x @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ rets, x @ y, [], [])))\<close> \<open>ver Pr {\<phi>} (Exhale (rename_pred P (args @ rets, x @ y, l, modif s)) ; Havoc y ; Inhale (rename_pred Q (args @ rets, x @ y, l, modif s)))\<close> sem_asso sem_seq_single ver_asso by blast
      then show ?thesis
        using calculation(1) elem_sem subset_eq by smt
    qed
    ultimately show ?thesis by blast
  qed
  then have "{h_comp |\<phi>| y} \<oplus>\<oplus> {?r} \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?Q >> sem Pr {\<phi>} ?m"
    using subset_smaller by blast

  moreover have pre_induct: "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr new_s \<and> SC Pr n A new_l new_s \<and> no_inter A new_l \<and> set (modif new_s) \<subseteq> set new_l"
  proof -
    have "ver_program Pr \<and> wf_program Pr" using asm by simp
    moreover have "set (modif new_s) \<subseteq> set new_l"
      using assms(4) modif_in_read by auto
    moreover have "wf_stmt Pr new_s" using wf_stmt_wf_renaming[of ?t Pr s]
      using \<open>wf_renaming (args @ rets, x @ y, l, modif s)\<close> \<open>wf_stmt Pr s\<close> assms(3) by blast
    moreover have "SC Pr n A new_l new_s" using sc_method_implies_new[of new_s s args rets x y l new_l Pr n A m] assms asm
      by metis
    moreover have "no_inter A new_l"
    proof -
      have "no_inter A l" using asm by linarith
      moreover have "set l \<subseteq> set new_l" using assms(4) by simp
      ultimately show ?thesis
        using no_inter_def no_inter_single_def by auto
    qed
    ultimately show ?thesis by blast
  qed

  moreover have "framing Pr A (inline Pr n new_l new_s)" using sc_method_implies_new[of new_s s args rets x y l new_l Pr n A m P Q]
    using asm assms(2) assms(3) assms(4) by presburger

  moreover obtain \<phi>'' where ineq'': "\<phi>'' \<in> A" "\<phi>' << \<phi>''" using asm by blast
  then have "\<phi> << \<phi>''" using asm using smaller_trans by blast

  moreover have "{ |\<phi>| } >> h x \<oplus>\<oplus> h y"
  proof -
    have "ver Pr {\<phi>} ?m" using asm by simp
    then have "set x \<union> set y \<subseteq> \<sigma> \<phi>" using ver_method_real[of Pr m args rets P Q s \<phi> y x] assms(2) by simp
    then show ?thesis
      by (metis h_bigger havoc_concat set_append store_pure)
  qed

  have "{i_phi} >> h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?P"
  proof -
    have "{i_phi} >> Inh ?P"
      using \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>i \<in> Inh (rename_pred P (args @ rets, x @ y, l, modif s))\<close> bigger_set_def commutative_monoid.s_core_def commutative_monoid.smaller_def commutative_monoid_axioms by fastforce
    moreover have "{i_phi} >> h x \<oplus>\<oplus> h y"
      using \<open>core_i_phi << i_phi\<close> \<open>core_i_phi = |\<phi>|\<close> \<open>{|\<phi>|} >> h x \<oplus>\<oplus> h y\<close> bigger_set_def smaller_trans by fastforce
    ultimately show ?thesis
      by (metis h_set_pure havoc_concat simple_set_add_comm)
  qed

  then obtain xx where "xx \<in> h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?P" "xx << i_phi"
    using bigger_set_def by auto
  moreover have "ver Pr {xx} new_s"
    using \<open>ver Pr (h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh (rename_pred P (args @ rets, x @ y, l, modif s))) (rename s (args @ rets, x @ y, l, modif s)) \<and> sem Pr (h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh (rename_pred P (args @ rets, x @ y, l, modif s))) (rename s (args @ rets, x @ y, l, modif s)) >> Inh (rename_pred Q (args @ rets, x @ y, l, modif s))\<close> calculation(4) v_singleton 
    assms(3) calculation(5) by blast

  moreover have "i_phi << \<phi>''"
  proof -
    have "i_phi << \<phi>"
      using \<open>Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some (h_comp r y)\<close> \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> smaller_def by fastforce
    moreover have "\<phi> << \<phi>''" using ineq''(2) asm
      using smaller_trans by blast
    ultimately show ?thesis
      using smaller_trans by blast
  qed

  ultimately have res: "ver Pr {i_phi} (inline Pr n new_l new_s) \<and> sem Pr {i_phi} (inline Pr n new_l new_s) >> sem Pr {xx} new_s"
    using instantiate_SP[of Pr n A new_l new_s i_phi xx] pre_induct \<open>\<phi>'' \<in> A\<close> assms(1) by blast

  have "inline Pr (Suc n) l ?m = inline Pr n new_l new_s"
    by (metis assms(2) assms(3) assms(4) get_method_inlined)

  then have "ver Pr {\<phi>'} (inline Pr (Suc n) l ?m) \<and> ver Pr {\<phi>} (inline Pr (Suc n) l ?m)"
  proof -
    have "ver Pr {i_phi} (inline Pr (Suc n) l ?m)"
      using \<open>inline Pr (Suc n) l (MethodCall y m x) = inline Pr n new_l new_s\<close> res by auto
    moreover have "ssafeMono Pr A (inline Pr (Suc n) l ?m)"
      using \<open>framing Pr A (inline Pr n new_l new_s)\<close> \<open>inline Pr (Suc n) l (MethodCall y m x) = inline Pr n new_l new_s\<close> semantics_algebra.smono_def semantics_algebra_axioms by fastforce
    moreover have "i_phi << \<phi>"
      using \<open>Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some (h_comp r y)\<close> \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> smaller_def by fastforce
    then have "i_phi << \<phi>'" using asm
      using smaller_trans by blast
    ultimately show ?thesis
      using \<open>i_phi << \<phi>\<close> asm smaller_trans ssafeMono_singleton by blast
  qed

  moreover have "set (modif (inline Pr n new_l new_s)) \<inter> \<sigma> \<phi> \<subseteq> set y"
  proof -
    have "set new_l \<inter> set (modif (inline Pr n new_l new_s)) \<subseteq> set (modif new_s)" using no_inter_inline_general[of Pr new_s new_l n] asm assms(3)
      pre_induct by simp
    moreover have "set l \<subseteq> set new_l" using assms(4) by simp
    moreover have "\<sigma> \<phi> \<subseteq> set l"
    proof -
      have "no_inter_single \<phi>'' l" using asm no_inter_def
        using ineq''(1) by blast
      then have "\<sigma> \<phi>'' \<subseteq> set l"
        by (simp add: no_inter_single_def)
      moreover have "\<sigma> \<phi> \<subseteq> \<sigma> \<phi>''"
        using \<open>\<phi> << \<phi>''\<close>
        by (metis Un_commute core_properties(1) pure_smaller_ok smaller_core_comp store_add store_pure subset_Un_eq)
      ultimately show ?thesis by blast
    qed
    moreover have "set l \<inter> set (modif ?s) \<subseteq> set y"
    proof -
      have "set (modif ?s) \<inter> (set (args @ rets) \<union> set l) \<subseteq> set (x @ y)"
        using rename_removes_vars_modif[of "args @ rets" "x @ y" l "modif s" s]
        using \<open>wf_renaming (args @ rets, x @ y, l, modif s)\<close> 
        by blast

      then have "set (modif ?s) \<inter> (set (args @ rets) \<union> set l) \<subseteq> set (x @ y)"
        using \<open>wf_renaming (args @ rets, x @ y, l, modif s)\<close> rename_modif_list rename_removes_vars_list
        by blast

      moreover have "set x \<inter> set (modif ?s) = {}"
      proof -
        have "wf_renaming (args @ rets, x @ y, l, modif s) \<and>
    length args = length x \<and> set args \<inter> set (modif s) = {} \<and> set (modif s) \<subseteq> set (read s)"
        proof -
          have "wf_renaming ?t"
            using \<open>wf_renaming (args @ rets, x @ y, l, modif s)\<close> by blast
          moreover have "length args = length x"
          proof -
            have "wf_stmt Pr ?m" using asm by simp
            then show ?thesis using assms
              by (metis wf_method_exists_equiv)
          qed
          moreover have "set (modif s) \<subseteq> set (read s)"
            by (simp add: modif_in_read)
          moreover have "set args \<inter> set (modif s) = {}"
          proof -
            have "wf_stmt Pr ?m" using asm by simp
            then show ?thesis using assms
              using wf_meth wf_method.simps by blast
          qed
          ultimately show ?thesis by blast
        qed
        then show ?thesis
          by (simp add: rename_modif_no_inter)
      qed
      have "set (modif ?s) \<inter> (set (args @ rets) \<union> set l) \<subseteq> set y"
      proof (rule subsetI)
        fix xa assume xain: "xa \<in> set (modif ?s) \<inter> (set (args @ rets) \<union> set l)"
        then have "xa \<in> set x \<union> set y"
          using calculation by auto
        moreover have "xa \<notin> set x" using xain \<open>set x \<inter> set (modif ?s) = {}\<close>
          by blast
        ultimately show "xa \<in> set y"
          by simp
      qed

      then show ?thesis by blast
    qed
    then show ?thesis
      using assms(3) calculation(1) calculation(2) calculation(3) by blast
  qed

  moreover have "sem Pr {\<phi>'} (inline Pr n new_l new_s) >> {h_comp |\<phi>| y} \<oplus>\<oplus> {?r} \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?Q"
  proof -
    have "sem Pr {\<phi>'} (inline Pr n new_l new_s) >> sem Pr {\<phi>} (inline Pr n new_l new_s)"
      using \<open>framing Pr A (inline Pr n new_l new_s)\<close> \<open>inline Pr (Suc n) l (MethodCall y m x) = inline Pr n new_l new_s\<close> asm calculation smonoOut_singleton smono_def by auto
    then have "... = sem Pr ({i_phi} \<oplus>\<oplus> {?r}) (inline Pr n new_l new_s)"
    proof -
      have "Some \<phi> = Some i_phi \<oplus> Some ?r"
        by (simp add: \<open>Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some (h_comp r y)\<close> \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close>)
      then show ?thesis
        using simple_set_add by auto
    qed
    moreover have "set (modif (inline Pr n new_l new_s)) \<inter> \<sigma> ?r = {}"
    proof -
      have "set (modif (inline Pr n new_l new_s)) \<inter> \<sigma> ?r \<subseteq> set y"
      proof -
        have "\<sigma> ?r \<subseteq> \<sigma> \<phi>" 
          by (metis \<open>Some \<phi> = Some i \<oplus> (s_core \<phi> \<oplus> Some (h_comp r y))\<close> \<open>Some core_i_phi_r = Some core_i_phi \<oplus> Some (h_comp r y)\<close> \<open>Some core_i_phi_r = s_core i \<oplus> (s_core \<phi> \<oplus> Some (h_comp r y))\<close> \<open>core_i_phi = |\<phi>|\<close> commutative_monoid.s_core_def commutative_monoid_axioms store_add store_pure sup.order_iff)
        then show ?thesis 
          using \<open>set (modif (inline Pr n new_l new_s)) \<inter> \<sigma> \<phi> \<subseteq> set y\<close> by blast
      qed
      then show ?thesis
        using \<open>\<sigma> (h_comp r y) \<inter> set y = {}\<close> by auto
    qed

    moreover have "(\<exists>s a. Some s = Some i_phi \<oplus> Some ?r \<and> s << a \<and> a \<in> A)" 
      using \<open>Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some (h_comp r y)\<close> \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>\<phi> << \<phi>''\<close> ineq''(1) by auto
    ultimately have "sem Pr ({i_phi} \<oplus>\<oplus> {?r}) (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {?r}"
      using \<open>framing Pr A (inline Pr n new_l new_s)\<close> instantiate_framing res by blast
    then have "sem Pr {\<phi>'} (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {?r}"
      using \<open>sem Pr {\<phi>'} (inline Pr n new_l new_s) >> sem Pr {\<phi>} (inline Pr n new_l new_s)\<close> \<open>sem Pr {\<phi>} (inline Pr n new_l new_s) = sem Pr ({i_phi} \<oplus>\<oplus> {h_comp r y}) (inline Pr n new_l new_s)\<close> bigger_set_trans by presburger

    moreover have "sem Pr {i_phi} (inline Pr n new_l new_s) >> sem Pr {xx} new_s"
      using res by linarith

    let ?core_y = "h_comp |\<phi>| y"

    have "set (modif (inline Pr n new_l new_s)) \<inter> \<sigma> ?core_y = {}"
    proof -
      have "set (modif (inline Pr n new_l new_s)) \<inter> \<sigma> ?core_y \<subseteq> set y"
      proof -
        have "\<sigma> ?core_y \<subseteq> \<sigma> \<phi>"
          using h_comp_store store_pure by auto
        then show ?thesis 
          using \<open>set (modif (inline Pr n new_l new_s)) \<inter> \<sigma> \<phi> \<subseteq> set y\<close> by blast
      qed
      then show ?thesis
        using h_comp_store by auto
    qed

    moreover have "(\<exists>s a. Some s = Some i_phi \<oplus> Some ?core_y \<and> s << a \<and> a \<in> A)"
      by (metis \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>i_phi << \<phi>''\<close> associative commutative core_inv h_comp_sum ineq''(1) s_core_def)
    ultimately have "sem Pr ({i_phi} \<oplus>\<oplus> {?core_y}) (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {?core_y}"
      using \<open>framing Pr A (inline Pr n new_l new_s)\<close> instantiate_framing res by blast

    then have inter_res: "sem Pr {\<phi>'} (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {?r} \<oplus>\<oplus> {?core_y}"
    proof -
      have "{i_phi} \<oplus>\<oplus> {?core_y} = {i_phi}"
        using \<open>core_i_phi << i_phi\<close> \<open>core_i_phi = |\<phi>|\<close> core_properties(1) h_comp_smaller pure_smaller_ok simple_set_add smaller_pure smaller_trans by blast
      moreover have "sem Pr {\<phi>'} (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {?r}"
        using \<open>sem Pr {\<phi>'} (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {h_comp r y}\<close> by blast
      moreover have "sem Pr {i_phi} (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {?core_y}" 
        using \<open>sem Pr ({i_phi} \<oplus>\<oplus> {h_comp |\<phi>| y}) (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {h_comp |\<phi>| y}\<close> calculation(1) by auto
      ultimately have "sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {?r} >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {?core_y} \<oplus>\<oplus> {?r}"
        using plus_and_bigger_set by blast
      then show ?thesis
        by (smt \<open>sem Pr {\<phi>'} (inline Pr n new_l new_s) >> sem Pr {i_phi} (inline Pr n new_l new_s) \<oplus>\<oplus> {h_comp r y}\<close> bigger_set_trans set_add_asso simple_set_add_comm)
    qed

    moreover have "sem Pr {xx} new_s >> Inh ?Q"
    proof -
      have "sem Pr {xx} ?s >> sem Pr (h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh ?P) ?s" 
        by (meson \<open>xx \<in> h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh (rename_pred P (args @ rets, x @ y, l, modif s))\<close> bigger_set_def elem_sem smaller_refl)
      then show ?thesis using assms(3)
        using \<open>ver Pr (h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh (rename_pred P (args @ rets, x @ y, l, modif s))) (rename s (args @ rets, x @ y, l, modif s)) \<and> sem Pr (h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh (rename_pred P (args @ rets, x @ y, l, modif s))) (rename s (args @ rets, x @ y, l, modif s)) >> Inh (rename_pred Q (args @ rets, x @ y, l, modif s))\<close> bigger_set_trans by blast
    qed

    moreover have "sem Pr {xx} new_s >> h y"
    proof -
      have "set y \<subseteq> \<sigma> xx"
      proof -
        obtain hx hy ip where "Some xx = Some hx \<oplus> Some hy \<oplus> Some ip" "hy \<in> h y" "hx \<in> h x" "ip \<in> Inh ?P"
          by (metis \<open>xx \<in> h x \<oplus>\<oplus> h y \<oplus>\<oplus> Inh (rename_pred P (args @ rets, x @ y, l, modif s))\<close> set_add_elem)
        then have "hy << xx"
          by (smt associative commutative h_pure pure_smaller_ok smaller_def smaller_refl)
        then have "\<sigma> hy \<subseteq> \<sigma> xx" 
          using \<open>hy \<in> h y\<close> h_pure pure_smaller_ok store_add by blast
        then show ?thesis 
          using \<open>hy \<in> h y\<close> h_store by blast
      qed
      then show ?thesis using store_modif_sem[of Pr new_s xx] assms(3)
        by (metis Un_subset_iff \<open>ver Pr {xx} new_s\<close> biggerSingletonI h_bigger pre_induct subset_Un_eq)
    qed

    ultimately show ?thesis 
    proof -
      have "sem Pr {xx} new_s >> Inh ?Q \<oplus>\<oplus> h y"
        using \<open>sem Pr {xx} new_s >> Inh (rename_pred Q (args @ rets, x @ y, l, modif s))\<close> \<open>sem Pr {xx} new_s >> h y\<close> h_set_pure by blast
      then have "sem Pr {\<phi>'} (inline Pr n new_l new_s) >> Inh ?Q \<oplus>\<oplus> h y \<oplus>\<oplus> {?r} \<oplus>\<oplus> {?core_y}"
      proof -
        have "sem Pr {\<phi>'} (inline Pr n new_l new_s) >> sem Pr {xx} new_s \<oplus>\<oplus> {?r} \<oplus>\<oplus> {?core_y}"
          using \<open>sem Pr {i_phi} (inline Pr n new_l new_s) >> sem Pr {xx} new_s\<close> bigger_set_trans inter_res plus_and_bigger_set by blast
        moreover have "sem Pr {xx} new_s \<oplus>\<oplus> {?r} \<oplus>\<oplus> {?core_y} >> Inh ?Q \<oplus>\<oplus> h y \<oplus>\<oplus> {?r} \<oplus>\<oplus> {?core_y}"
          using \<open>sem Pr {xx} new_s >> Inh (rename_pred Q (args @ rets, x @ y, l, modif s)) \<oplus>\<oplus> h y\<close> plus_and_bigger_set by blast
        ultimately show ?thesis 
          using bigger_set_trans by blast
      qed
      then show ?thesis
        using set_add_asso simple_set_add_comm by auto
    qed
  qed
  then show "ver Pr {\<phi>'} (inline Pr (Suc n) l ?m) \<and> sem Pr {\<phi>'} (inline Pr (Suc n) l ?m) >> sem Pr {\<phi>} ?m"
    using \<open>inline Pr (Suc n) l (MethodCall y m x) = inline Pr n new_l new_s\<close> \<open>{h_comp |\<phi>| y} \<oplus>\<oplus> {h_comp r y} \<oplus>\<oplus> h y \<oplus>\<oplus> Inh (rename_pred Q (args @ rets, x @ y, l, modif s)) >> sem Pr {\<phi>} (MethodCall y m x)\<close> bigger_set_trans calculation by presburger
qed

lemma bigger_set_singleton:
  assumes "\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. sem Pr {a} s1 >> sem Pr {b} s2)"
  shows "sem Pr A s1 >> sem Pr B s2"
proof -
  have "\<And>sa. sa \<in> sem Pr A s1 \<Longrightarrow> (\<exists>sb \<in> sem Pr B s2. sb << sa)"
  proof -
    fix sa assume "sa \<in> sem Pr A s1"
    then obtain a where "a \<in> A" "sa \<in> sem Pr {a} s1" using elem_sem by blast
    then obtain b where "b \<in> B" "sem Pr {a} s1 >> sem Pr {b} s2" using assms by blast
    moreover have "sem Pr {b} s2 \<subseteq> sem Pr B s2" using calculation(1) elem_sem by blast
    ultimately show "\<exists>sb \<in> sem Pr B s2. sb << sa"
      by (meson \<open>sa \<in> sem Pr {a} s1\<close> sep_algebra.bigger_set_def sep_algebra_axioms subset_eq)
  qed
  then show ?thesis by (simp add: bigger_set_def)
qed

lemma f_singleton:
  "(\<Union>a\<in>A. f {a} b) = f A b" using f_def by auto

lemma sem_assume_filter:
  assumes "ver Pr A (Assume b)"
  shows "sem Pr A (Assume b) = f A b"
proof -
  have "\<And>a. a \<in> A \<Longrightarrow> sem Pr {a} (Assume b) = f {a} b"
  proof -
    fix a assume "a \<in> A"
    then have "ver Pr {a} (Assume b)"
      using assms v_singleton by blast
    then show "sem Pr {a} (Assume b) = f {a} b"
    proof (cases "b a")
      case None
      then have "\<not> ver Pr {a} (Assume b)"
        by (simp add: ver_assume)
      then show ?thesis 
        using \<open>ver Pr {a} (Assume b)\<close> by blast
    next
      case (Some r)
      then show ?thesis
      proof (cases r)
        case True
        then have "sem Pr {a} (Assume b) = {a}" using \<open>a \<in> A\<close> assms sem_assume_true semantics.simps(2) ver_def
          by (simp add: Some well_defined_assert_def)
        moreover have "f {a} b = {a}" using \<open>a \<in> A\<close> assms sem_assume_true semantics.simps(2) ver_def
          Some well_defined_assert_def f_def[of "{a}" b] True
          by auto
        ultimately show ?thesis by auto
      next
        case False
        then have "sem Pr {a} (Assume b) = {}" using Some 
          using sem_assume_false by auto
        then show ?thesis using f_def False Some by auto
      qed
    qed
  qed
  then have "sem Pr A (Assume b) = (\<Union>a\<in>A. f {a} b)"
    by auto
  then show ?thesis by (simp add: f_singleton)
qed

lemma f_inclusion:
  "f A b \<subseteq> A" using f_def by auto

lemma strongerI:
  "(\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. b << a)) \<Longrightarrow> A >> B"
  by (simp add: bigger_set_def)

lemma wfm_f:
  assumes "wfm Pr b"
      and "A >> B"
      and "ver Pr B (Assume b)"
    shows "f A b >> f B b"
proof (rule strongerI)
  fix a assume asm: "a \<in> f A b"
  then have "b a = Some True" using f_def by simp
  then have "{a} >> B"
    by (meson asm assms(2) bigger_set_forall f_inclusion in_mono)
  then have "ver Pr {a} (Assume b) \<and> sem Pr {a} (Assume b) >> sem Pr B (Assume b)"
    using \<open>a \<in> f A b\<close> assms(1) assms(3) bigger_set_def f_inclusion in_mono singletonD smaller_refl smonoOut_def smono_def ssafeMono_singleton v_singleton wfm_def
    by smt
  then obtain bb where "bb \<in> sem Pr B (Assume b)" "bb << a"
    by (metis \<open>b a = Some True\<close> bigger_set_def insertI1 sem_assume_true semantics.simps(2) ver_def)
  then have "bb \<in> f B b" using f_def ver_assume
    using assms(3) sem_assume_filter by fastforce
  then show "\<exists>b\<in>f B b. b << a"
    using \<open>bb << a\<close> by blast
qed

lemma if_assume_then_true:
  assumes "x \<in> sem Pr A (Assume b)"
      and "ver Pr A (Assume b)"
  shows "b x = Some True"
  using assms(1) assms(2) f_def member_filter sem_assume_filter by fastforce

lemma lnot_false_true:
  "b x = Some True \<longleftrightarrow> lnot b x = Some False"
  "lnot b x = Some True \<longleftrightarrow> b x = Some False"
  apply (metis (mono_tags, lifting) lnot_def option.distinct(1) option.sel wfm_not_same)
  by (metis (mono_tags, lifting) lnot_def option.distinct(1) option.sel wfm_not_same)

lemma after_while:
  assumes "ver Pr A (While b I s)"
      and "sa \<in> sem Pr A (While b I s)"
    shows "b sa = Some False"
proof -
  obtain a where "a \<in> A" "sa \<in> sem Pr {a} (While b I s)"
    using assms(2) elem_sem by blast
  then have "sem Pr {a} (While b I s) = sem Pr {a} (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I ; Assume (lnot b))" 
    using Sup.SUP_cong assms(1) v_singleton semantics_algebra_axioms s_singleton sem_loop
    by smt
  then have "sa \<in> sem Pr (sem Pr {a} (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I)) (Assume (lnot b))"
    by (metis \<open>a \<in> A\<close> \<open>sa \<in> sem Pr {a} (While b I s)\<close> assms(1) sem_seq_single v_singleton ver_loop)
  then have "lnot b sa \<noteq> None"
    by (metis \<open>a \<in> A\<close> assms(1) if_assume_then_true option.discI v_singleton ver_loop ver_seq)
  moreover have "lnot b sa = Some True"
  proof -
    have "ver Pr (sem Pr {a} (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I)) (Assume (lnot b))"
      by (meson \<open>a \<in> A\<close> assms(1) v_singleton ver_loop ver_seq_single)
    then show ?thesis 
      using \<open>sa \<in> sem Pr (sem Pr {a} (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I)) (Assume (lnot b))\<close> if_assume_then_true by blast
  qed
  then show "b sa = Some False"
    by (meson lnot_false_true(2))
qed

lemma general_same_f:
  assumes "\<And>a. a \<in> A \<Longrightarrow> b a = Some True"
  shows "f A b = A"
  using assms f_def by auto

lemma after_while_same_f:
  assumes "ver Pr A (While b I s)"
  shows "f (sem Pr A (While b I s)) (lnot b) = sem Pr A (While b I s)"
  using after_while assms general_same_f
  by (meson lnot_false_true(2))

(*
lemma wfm_bigger:
  assumes "c << a"
      and "wfm Pr b"
      and "b c"
      and "ver Pr {c} (Assume b)"
    shows "b a"
proof -
  have "wfm Pr (lnot b)" using assms(2) wfm_not by auto
  moreover have "{a} >> {c}" using assms(1) bigger_set_def by blast
  ultimately have "f {a} (lnot b) >> f {c} (lnot b)" using wfm_f[of Pr "lnot b" "{a}" "{c}"]
    by (metis assms(4) can_read_not semantics.simps(2) ss.distinct(1) ver_def)
  moreover have "f {c} (lnot b) = {}" using assms(3) f_def lnot_def
    by (metis f_inclusion insertI1 member_filter subset_singletonD)
  then show ?thesis
    by (metis bigger_set_def calculation empty_iff general_same_f insert_iff lnot_def)
qed
*)

lemma assume_false_sem:
  "sem Pr A (Assume lfalse) = {}" by (metis elem_sem empty_iff equals0I lfalse_def sem_assume_false)

lemma verif_exhale_exists_decompo:
  assumes "ver Pr {\<phi>} (Exhale I)"
      and "wf_assert I"
    shows "\<exists>i r. i \<in> Inh I \<and> Some \<phi> = Some i \<oplus> Some r"
proof -
  have "{\<phi>} >> Inh I" using assms(1) assms(2) exhale_verif local.wf_assert_def by auto
  then show ?thesis using bigger_set_def smaller_def by auto
qed

lemma assume_not_bigger:
  assumes "ver Pr {\<phi>} (While b I s)"
      and "wf_assert I"
    shows "{\<phi>} >> sem Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I)"
proof -
  have "ver Pr {\<phi>} (Exhale I)" using assms(1) sem_seq ver_loop
    by (simp add: ver_seq)
  obtain i r where "i \<in> Inh I" "Some \<phi> = Some i \<oplus> Some r"
    by (meson \<open>ver Pr {\<phi>} (Exhale I)\<close> assms(2) verif_exhale_exists_decompo semantics_algebra_axioms)
  then obtain i_phi where "Some i_phi = s_core i \<oplus> Some r"
    by (metis associative commutative decompo_new_plus option.distinct(1) option.exhaust_sel plus.simps(2))
  define V where "V = filter_sigma \<phi> (modif s)"
  then have "{h_comp i_phi V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I >> sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I)"
  proof -
    have "{i_phi} >> sem Pr {\<phi>} (Exhale I)"
      by (meson \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>Some i_phi = s_core i \<oplus> Some r\<close> \<open>i \<in> Inh I\<close> \<open>ver Pr {\<phi>} (Exhale I)\<close> assms(2) core_i_phi_exhale exhale_verif subset_smaller)
    moreover have "ver Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I)" 
      using V_def assms(1) ver_loop ver_seq by blast
    moreover have "mono Pr {i_phi} (Havoc V)" 
      using havoc_smono mono_smono by blast
    ultimately have "ver Pr {i_phi} (Havoc V) \<and> sem Pr {i_phi} (Havoc V) >> sem Pr {\<phi>} (Exhale I ; Havoc V)" 
      by (smt bigger_set_def mono_smono sem_seq smaller_refl smonoOut_def smono_def ssafeMono_singleton v_singleton ver_seq)
    moreover have "mono Pr (sem Pr {i_phi} (Havoc V)) (Inhale I)"
      using assms(2) inhale_smono mono_smono by blast
    ultimately have "ver Pr (sem Pr {i_phi} (Havoc V)) (Inhale I) \<and> sem Pr (sem Pr {i_phi} (Havoc V)) (Inhale I) >> sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I)" 
      by (smt \<open>ver Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I)\<close> assms(2) bigger_set_def plus_and_bigger_set sem_inhale sem_seq_single ver_inhale ver_seq well_defined_assert_monoin well_defined_assert_set_def)
    moreover have "sem Pr (sem Pr {i_phi} (Havoc V)) (Inhale I) = {h_comp i_phi V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I" 
      using \<open>ver Pr {i_phi} (Havoc V) \<and> sem Pr {i_phi} (Havoc V) >> sem Pr {\<phi>} (Exhale I ; Havoc V)\<close> calculation sem_havoc sem_inhale ver_inhale by force
    ultimately show ?thesis by simp
  qed
  then have "{\<phi>} >> {h_comp i_phi V} \<oplus>\<oplus> Inh I"
  proof -
    have "Some \<phi> = Some i \<oplus> Some i_phi"
      by (metis (full_types) \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>Some i_phi = s_core i \<oplus> Some r\<close> associative core_properties(1) core_properties(2) commutative_monoid.s_core_def commutative_monoid_axioms pure_smaller_ok)
    moreover have "h_comp i_phi V << i_phi" by (simp add: h_comp_smaller)
    ultimately have "{\<phi>} >> {h_comp i_phi V} \<oplus>\<oplus> {i}"
      by (metis bigger_set_forall h_comp_smaller plus.simps(1) plus_and_bigger_set rel_bigger_add_set simple_set_add simple_set_add_comm singletonI smaller_def)
    then show ?thesis
    proof -
      have "Inh I >> Inh I"
        by (simp add: subset_smaller)
      then show ?thesis
        by (metis (no_types) \<open>i \<in> Inh I\<close> \<open>{\<phi>} >> {h_comp i_phi V} \<oplus>\<oplus> {i}\<close> sep_algebra.bigger_set_forall sep_algebra.bigger_set_trans sep_algebra.plus_and_bigger_set sep_algebra_axioms simple_set_add_comm)
    qed
  qed
  moreover have "{\<phi>} >> h V"
  proof -
    have "ver Pr {\<phi>} (Exhale I ; Havoc V)" using V_def assms(1) sem_seq ver_loop ver_seq by simp
    then obtain a where "a \<in> sem Pr {\<phi>} (Exhale I)"
      using \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>i \<in> Inh I\<close> \<open>ver Pr {\<phi>} (Exhale I)\<close> assms(2) exhale_sem_inh semantics_algebra_axioms wf_assert_def 
      by blast
    then have "\<sigma> \<phi> = \<sigma> a"
    proof -
      have "\<sigma> \<phi> \<subseteq> \<sigma> a \<and> \<sigma> a \<subseteq> \<sigma> \<phi> \<union> set (modif (Exhale I))" using store_modif_sem[of Pr "Exhale I" \<phi> a]
        using \<open>a \<in> sem Pr {\<phi>} (Exhale I)\<close> \<open>ver Pr {\<phi>} (Exhale I)\<close>
        using assms(2) wf_assert_def wf_stmt.simps(6)
        using le_supI1 store_same_pred_supp_exhale 
        by (metis subset_refl)
      then show ?thesis by auto
    qed
    then have "set V \<subseteq> \<sigma> \<phi>"
      by (metis \<open>a \<in> sem Pr {\<phi>} (Exhale I)\<close> \<open>ver Pr {\<phi>} (Exhale I ; Havoc V)\<close> v_singleton semantics_algebra_axioms ver_havoc ver_seq)
    then show ?thesis
      by (simp add: h_bigger)
  qed
  ultimately have "{\<phi>} >> {h_comp i_phi V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I" 
    by (smt h_set_pure set_add_asso simple_set_add_comm)
  then show ?thesis using \<open>{h_comp i_phi V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I >> sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I)\<close> V_def set_add_asso simple_set_add_comm
    using bigger_set_trans by blast
qed

(*
lemma assume_not_bigger_real:
  assumes "ver Pr A (While b I s)"
      and "wf_assert I"
    shows "A >> sem Pr A (Exhale I ; Havoc (modif s) ; Inhale I)"
proof -
  have "\<And>a. a \<in> A \<Longrightarrow> (\<exists>sa \<in> sem Pr A (Exhale I ; Havoc (modif s) ; Inhale I). sa << a)"
  proof -
    fix a assume "a \<in> A"
    then have "{a} >> sem Pr {a} (Exhale I ; Havoc (filter_sigma a (modif s)) ; Inhale I)"
      using assms(1) assms(2) assume_not_bigger v_singleton by blast
    then show "(\<exists>sa \<in> sem Pr A (Exhale I ; Havoc (modif s) ; Inhale I). sa << a)"
      by (meson \<open>a \<in> A\<close> bigger_set_def elem_sem singleton_iff)
  qed
  then show ?thesis by (simp add: bigger_set_def)
qed
*)

lemma add_h_comp_core:
  assumes "Some x = Some a \<oplus> Some b"
      and "set V \<subseteq> \<sigma> x"
    shows "Some x = Some a \<oplus> Some (h_comp b V) \<oplus> s_core x"
  by (smt assms(1) associative commutative core_add core_properties(1) core_properties(2) h_comp_sum pure_smaller_ok s_core_def)

lemma h_comp_set_add_two:
  assumes "Some x = Some a \<oplus> Some b"
  shows "{h_comp x V} = {h_comp a V} \<oplus>\<oplus> {h_comp b V}"
proof -
  have "Some (h_comp x V) = Some (h_comp a V) \<oplus> Some (h_comp b V)"
    using assms h_comp_lin by blast
  then show ?thesis using simple_set_add by auto
qed

lemma h_comp_set_add:
  assumes "Some x = Some a \<oplus> Some b \<oplus> Some c \<oplus> Some d \<oplus> Some e"
  shows "{h_comp x V} = {h_comp a V} \<oplus>\<oplus> {h_comp b V} \<oplus>\<oplus> {h_comp c V} \<oplus>\<oplus>{h_comp d V} \<oplus>\<oplus> {h_comp e V}" (is "?a = ?b")
proof -
  obtain ab cde where "Some ab = Some a \<oplus> Some b" "Some cde = Some c \<oplus> Some d \<oplus> Some e"
    by (metis assms associative commutative option.exhaust plus.simps(3))
  then have "{h_comp x V} = {h_comp ab V} \<oplus>\<oplus> {h_comp cde V}"
    by (metis assms associative h_comp_set_add_two semantics_algebra_axioms)
  obtain cd where "Some cd = Some c \<oplus> Some d"
    by (metis \<open>Some cde = Some c \<oplus> Some d \<oplus> Some e\<close> option.discI plus.elims)
  then obtain "{h_comp ab V} = {h_comp a V} \<oplus>\<oplus> {h_comp b V}"
    "{h_comp cd V} = {h_comp c V} \<oplus>\<oplus> {h_comp d V}"
    "{h_comp cde V} = {h_comp cd V} \<oplus>\<oplus> {h_comp e V}"
    by (metis \<open>Some ab = Some a \<oplus> Some b\<close> \<open>Some cde = Some c \<oplus> Some d \<oplus> Some e\<close> h_comp_set_add_two)
  then show ?thesis by (simp add: \<open>{h_comp x V} = {h_comp ab V} \<oplus>\<oplus> {h_comp cde V}\<close> set_add_asso)
qed

lemma h_comp_sum_set_smaller_pure:
  assumes "pure a"
      and "a << b"
    shows "{h_comp a V} \<oplus>\<oplus> {h_comp b V} = {h_comp b V}"
  using assms(1) assms(2) h_comp_set_add_two pure_smaller_ok simple_set_add_comm by blast

lemma h_comp_smaller_elem:
  assumes "h_comp |a| V << x"
  shows "{h_comp |a| V} \<oplus>\<oplus> {h_comp |x| V} = {h_comp |x| V}"
  by (metis Diff_disjoint assms core_properties(1) core_properties(3) h_comp_store h_comp_not_here h_comp_only_pure h_comp_sum_set_smaller_pure pure_c smaller_core_comp)

lemma core_four:
  assumes "Some a = Some b \<oplus> Some c \<oplus> Some d \<oplus> Some e"
  shows "s_core a = s_core b \<oplus> s_core c \<oplus> s_core d \<oplus> s_core e"
proof -
  obtain bc de where "Some bc = Some b \<oplus> Some c" "Some de = Some d \<oplus> Some e"
    by (metis assms associative plus.elims)
  then obtain "s_core bc = s_core b \<oplus> s_core c" "s_core de = s_core d \<oplus> s_core e"
    "s_core a = s_core bc \<oplus> s_core de" by (metis assms associative core_add)
  then show ?thesis by (simp add: associative)
qed

lemma h_comp_set_add_four:
  assumes "Some x = Some a \<oplus> Some b \<oplus> Some c \<oplus> Some d"
  shows "{h_comp x V} = {h_comp a V} \<oplus>\<oplus> {h_comp b V} \<oplus>\<oplus> {h_comp c V} \<oplus>\<oplus>{h_comp d V}" (is "?a = ?b")
proof -
  obtain ab cd where "Some ab = Some a \<oplus> Some b" "Some cd = Some c \<oplus> Some d"
    by (metis assms associative plus.elims)
  then have "{h_comp x V} = {h_comp ab V} \<oplus>\<oplus> {h_comp cd V}"
    by (metis assms associative h_comp_set_add_two semantics_algebra_axioms)
  then obtain "{h_comp ab V} = {h_comp a V} \<oplus>\<oplus> {h_comp b V}"
    "{h_comp cd V} = {h_comp c V} \<oplus>\<oplus> {h_comp d V}"
    by (metis \<open>Some ab = Some a \<oplus> Some b\<close> \<open>Some cd = Some c \<oplus> Some d\<close> h_comp_set_add_two)
  then show ?thesis by (simp add: \<open>{h_comp x V} = {h_comp ab V} \<oplus>\<oplus> {h_comp cd V}\<close> set_add_asso)
qed

(*
lemma framing_set_singleton:
  assumes "\<sigma> r \<inter> set (modif s) = {}"
      and "ver Pr A s"
      and "framing Pr s"
    shows "sem Pr (A \<oplus>\<oplus> {r}) s >> sem Pr A s \<oplus>\<oplus> {r}"
proof -
  have "\<And>sar. sar \<in> sem Pr (A \<oplus>\<oplus> {r}) s \<Longrightarrow> (\<exists>y \<in> sem Pr A s \<oplus>\<oplus> {r}. y << sar)"
  proof -
    fix sar assume "sar \<in> sem Pr (A \<oplus>\<oplus> {r}) s"
    then obtain ar where "ar \<in> A \<oplus>\<oplus> {r}" "sar \<in> sem Pr {ar} s" using elem_sem by blast
    then obtain a where "a \<in> A" "Some ar = Some a \<oplus> Some r" using elem_add_set by auto
    moreover have "ver Pr {a} s" using assms(2) calculation(1) v_singleton by blast
    moreover have "ver Pr {a} s \<and> set (modif s) \<inter> \<sigma> r = {} \<longrightarrow> (sem Pr ({a} \<oplus>\<oplus> {r}) s >> (sem Pr {a} s \<oplus>\<oplus> {r}))"
      using assms(3) by simp
    ultimately have "sem Pr ({a} \<oplus>\<oplus> {r}) s >> sem Pr {a} s \<oplus>\<oplus> {r}" by (simp add: Int_commute assms(1))
    moreover have "{a} \<oplus>\<oplus> {r} = {ar}" by (simp add: \<open>Some ar = Some a \<oplus> Some r\<close> simple_set_add)
    ultimately obtain y where "y \<in> sem Pr {a} s \<oplus>\<oplus> {r}" "y << sar"
      using \<open>sar \<in> sem Pr {ar} s\<close> bigger_set_def by auto
    moreover have "y \<in> sem Pr A s \<oplus>\<oplus> {r}"
    proof -
      have "sem Pr {a} s \<subseteq> sem Pr A s" using s_singleton[of Pr A s] using \<open>a \<in> A\<close> by blast
      then show ?thesis using calculation(1) elem_add_set by fastforce
    qed
    then show "\<exists>y \<in> sem Pr A s \<oplus>\<oplus> {r}. y << sar" using calculation(2) by blast
  qed
  then show ?thesis using bigger_set_def by blast
qed
*)

lemma sigma_sem_havoc:
  assumes "ver Pr {a} (Havoc V)"
    and "x \<in> sem Pr {a} (Havoc V)"
  shows "\<sigma> x = \<sigma> a \<union> set V"
proof -
  obtain hv where "hv \<in> h V" "Some x = Some (h_comp a V) \<oplus> Some hv"
    using assms elem_add_set sem_havoc by auto
  then show ?thesis using h_comp_store h_store store_add by auto
qed

(*
lemma bigger_and_ver_assume:
  assumes "ver Pr B (Assume b)"
      and "wfm Pr b"
      and "A >> B"
    shows "f A b >> f B b"
      and "f A (lnot b) >> f B (lnot b)"
  using assms(1) assms(2) assms(3) wfm_f apply blast
proof -
  obtain "ver Pr B (Assume (lnot b))" "wfm Pr (lnot b)"
    by (metis assms(1) assms(2) can_read_not semantics.simps(2) ss.distinct(1) ver_def wfm_not)
  then show "f A (lnot b) >> f B (lnot b)" using assms(1) assms(2) assms(3) wfm_f by blast
qed

lemma wfm_f_and_sum:
  assumes "wfm Pr b"
      and "ver Pr A (Assume b)"
    shows "f (A \<oplus>\<oplus> D) b = f A b \<oplus>\<oplus> D" (is "?a = ?b")
proof -
  have "?a \<subseteq> ?b"
  proof (rule subsetI)
    fix x assume "x \<in> ?a"
    then obtain a d where "Some x = Some a \<oplus> Some d" "a \<in> A" "d \<in> D"
      by (metis f_def member_filter sep_algebra.set_add_elem sep_algebra_axioms)
    then have "b a"
    proof -
      have "b x" using \<open>x \<in> f (A \<oplus>\<oplus> D) b\<close> f_def by auto
      moreover have "a << x" using \<open>Some x = Some a \<oplus> Some d\<close> smaller_def by blast
      moreover have "ver Pr {a} (Assume b)" using \<open>a \<in> A\<close> assms(2) v_singleton by blast
      ultimately show ?thesis
      proof -
        have "\<forall>A. {x} >> A \<or> a \<notin> A"
          using \<open>a << x\<close> bigger_set_def by blast
        then show ?thesis
          by (metis (no_types) \<open>b x\<close> \<open>ver Pr {a} (Assume b)\<close> assms(1) bigger_set_def empty_iff general_same_f insert_iff sem_assume_false sem_assume_filter wfm_f)
      qed        
    qed
    then have "a \<in> f A b" by (simp add: \<open>a \<in> A\<close> f_def)
    then show "x \<in> ?b" using \<open>Some x = Some a \<oplus> Some d\<close> \<open>d \<in> D\<close> set_add_elem_reci by blast
  qed
  moreover have "?b \<subseteq> ?a"
  proof (rule subsetI)
    fix x assume "x \<in> ?b"
    then obtain a d where "a \<in> f A b" "d \<in> D" "Some x = Some a \<oplus> Some d" using set_add_elem by blast
    then have "b a" by (simp add: f_def)
    moreover have "a << x" using \<open>Some x = Some a \<oplus> Some d\<close> smaller_def by blast
    ultimately have "b x"
      using \<open>a \<in> f A b\<close> assms(1) assms(2) f_inclusion v_singleton wfm_bigger semantics_algebra_axioms subset_iff by blast
    then show "x \<in> ?a" using \<open>Some x = Some a \<oplus> Some d\<close> \<open>a \<in> f A b\<close> \<open>d \<in> D\<close> f_def set_add_elem_reci by auto
  qed
  ultimately show ?thesis by blast
qed

lemma not_empty_exhale:
  assumes "ver Pr {\<phi>} (Exhale P)"
      and "wf_assert P"
  shows "sem Pr {\<phi>} (Exhale P) \<noteq> {}"
  using assms(1) assms(2) local.wf_assert_def exhale_sem_inh semantics_algebra_axioms verif_exhale_exists_decompo by fastforce
*)

lemma not_empty_havoc:
  assumes "ver Pr {\<phi>} (Havoc V)"
  shows "sem Pr {\<phi>} (Havoc V) \<noteq> {}"
proof -
  have "set V \<subseteq> \<sigma> \<phi>" using assms ver_havoc by auto
  then have "{\<phi>} >> {h_comp \<phi> V} \<oplus>\<oplus> h V" by (simp add: bigger_h_single)
  then show ?thesis
    using assms bigger_set_def sem_havoc by auto
qed

lemma not_empty_comp:
  assumes "\<And>a. sem Pr {a} s1 \<noteq> {}"
    and "\<And>b. sem Pr {b} s2 \<noteq> {}"
    and "ver Pr {c} (s1; s2)"
  shows "sem Pr {c} (s1 ; s2) \<noteq> {}"
proof -
  obtain b where "b \<in> sem Pr {c} s1" by (meson assms(1) ex_in_conv)
  then obtain d where "d \<in> sem Pr {b} s2" using assms(2) by auto
  then show ?thesis
    using \<open>b \<in> sem Pr {c} s1\<close> assms(3) sem_seq by fastforce
qed

lemma h_comp_add_single:
  assumes "{a} = {b} \<oplus>\<oplus> {c}"
  shows "{h_comp a x} = {h_comp b x} \<oplus>\<oplus> {h_comp c x}"
  using assms h_comp_set_add_two set_add_elem by blast

lemma soundness_invariant_not_inlinable:
  assumes "\<not> inlinable s"
  shows "SP Pr n A l s"
  by (smt SC.elims(2) SP_I assms not_inlinable_id smonoOut_singleton smono_def ssafeMono_singleton)

lemma filter_sigma_in:
  "set (filter_sigma \<phi> V) = set V \<inter> \<sigma> \<phi>"
proof (induction V)
  case Nil
  then show ?case
    by (simp add: filter_sigma_def)
next
  case (Cons a V)
  then show ?case
    by (simp add: filter_sigma_def)
qed

subsection \<open>Loop case\<close>

lemma assume_mono_same_b:
  assumes "mono Pr A (Assume b)"
      and "b x = Some False \<or> b y = Some True"
      and "b x \<noteq> None"
      and "x << y"
      and "y << z"
      and "z \<in> A"
    shows "b x = b y"
proof -
  have "ver Pr {y} (Assume b) \<and> ver Pr {x} (Assume b)" using assms mono_def
    by (meson mono_smono smono_def ssafeMono_singleton ver_assume)
  then have "b y \<noteq> None \<and> b x \<noteq> None"
    by (simp add: ver_assume)
  have "sem Pr {y} (Assume b) >> sem Pr {x} (Assume b)"
    using assms mono_def
    by (meson singletonI triple_not_error_semantics ver_assume ver_def)
  then have "f {y} b >> f {x} b"
    by (smt assms(1) assms(3) assms(4) assms(5) assms(6) local.mono_def sem_assume_filter singletonD singletonI smaller_error ver_assume ver_def)
  then show ?thesis
  proof (cases "b x = Some False")
    case True
    then have "f {x} b = {}" using f_def by auto
    then have "f {y} b = {}"
      using \<open>f {y} b >> f {x} b\<close> bigger_set_def by auto
    then show ?thesis using f_def True
      using \<open>b y \<noteq> None \<and> b x \<noteq> None\<close> by fastforce
  next
    case False
    then have "f {y} b = {y}" 
      using assms(2) general_same_f by fastforce
    then show ?thesis 
      using False assms(2) assms(3) by auto
  qed
qed

lemma assume_mono_framing:
  assumes "mono Pr A (Assume b)"
  shows "framing Pr A (Assume b)"
proof (rule framingI)
  show "mono Pr A (Assume b)" using assms by simp
  fix a r assume asm: "(\<exists>s b. Some s = Some a \<oplus> Some r \<and> s << b \<and> b \<in> A) \<and> ver Pr {a} (Assume b) \<and> set (modif (Assume b)) \<inter> \<sigma> r = {}"
  then show "sem Pr ({a} \<oplus>\<oplus> {r}) (Assume b) >> sem Pr {a} (Assume b) \<oplus>\<oplus> {r}"
  proof (cases "{a} \<oplus>\<oplus> {r} = {}")
    case True
    then show ?thesis
      using asm simple_set_add by auto
  next
    case False
    then obtain ar where "Some ar = Some a \<oplus> Some r"
      using asm by blast
    then have "\<exists>b. ar << b \<and> b \<in> A" using asm
      by (metis option.inject)
    then have "ver Pr {ar} (Assume b)"
      by (meson \<open>Some ar = Some a \<oplus> Some r\<close> asm assms insertI1 mono_smono orig_neutral commutative_monoid.smaller_def commutative_monoid_axioms smono_def ssafeMono_singleton)
    then have "b ar \<noteq> None"
      by (simp add: ver_assume)
    then show ?thesis
    proof (cases "b ar = Some True")
      case True
      then have "sem Pr ({a} \<oplus>\<oplus> {r}) (Assume b) = {ar}"
        using \<open>Some ar = Some a \<oplus> Some r\<close> simple_set_add well_defined_assert_def by force
      moreover have "b a = Some True" 
        using assume_mono_same_b[of Pr A b a ar] asm
        by (metis True \<open>Some ar = Some a \<oplus> Some r\<close> assms smaller_def ver_assume)
      ultimately show ?thesis
        using \<open>Some ar = Some a \<oplus> Some r\<close> simple_set_add subset_smaller well_defined_assert_def by fastforce
    next
      case False
      then have "b ar = Some False"
        using \<open>b ar \<noteq> None\<close> by auto
      then show ?thesis 
        by (metis \<open>Some ar = Some a \<oplus> Some r\<close> biggerSingletonI empty_iff sem_assume_false simple_set_add)
    qed
  qed
qed

lemma bigger_if_ver:
  assumes "ver Pr A (If s1 s2)"
  shows "sem Pr A s1 >> sem Pr A (If s1 s2)"
    and "sem Pr A s2 >> sem Pr A (If s1 s2)"
  using assms sem_if subset_smaller by auto

lemma framing_if:
  assumes "framing Pr A s1"
      and "framing Pr A s2"
    shows "framing Pr A (If s1 s2)"
proof (rule framingI)
  show "mono Pr A (If s1 s2)"
    using assms(1) assms(2) mono_if mono_smono by auto
  fix a r assume asm: "(\<exists>s b. Some s = Some a \<oplus> Some r \<and> s << b \<and> b \<in> A) \<and> ver Pr {a} (stmt.If s1 s2) \<and> set (modif (stmt.If s1 s2)) \<inter> \<sigma> r = {}"
  then obtain ar where "\<exists>b. Some ar = Some a \<oplus> Some r \<and> ar << b \<and> b \<in> A" by blast
  show "sem Pr ({a} \<oplus>\<oplus> {r}) (stmt.If s1 s2) >> sem Pr {a} (stmt.If s1 s2) \<oplus>\<oplus> {r}"
  proof (rule greaterI)
    fix y assume "y \<in> sem Pr ({a} \<oplus>\<oplus> {r}) (stmt.If s1 s2)"
    moreover have "ver Pr ({a} \<oplus>\<oplus> {r}) (stmt.If s1 s2)"
    proof -
      have "a << ar"
        using \<open>\<exists>b. Some ar = Some a \<oplus> Some r \<and> ar << b \<and> b \<in> A\<close> smaller_def by blast
      moreover have "mono Pr A (If s1 s2)"
        using assms(1) assms(2) mono_if mono_smono by auto
      ultimately have "ver Pr {ar} (If s1 s2)" 
        using \<open>\<exists>b. Some ar = Some a \<oplus> Some r \<and> ar << b \<and> b \<in> A\<close> asm mono_smono smono_def ssafeMono_singleton by blast
      then show ?thesis
        using \<open>\<exists>b. Some ar = Some a \<oplus> Some r \<and> ar << b \<and> b \<in> A\<close> simple_set_add by auto
    qed
    then show "\<exists>x\<in>sem Pr {a} (stmt.If s1 s2) \<oplus>\<oplus> {r}. x << y"
    proof (cases "y \<in> sem Pr ({a} \<oplus>\<oplus> {r}) s1")
      case True
      moreover have "ver Pr {a} s1 \<and> set (modif s1) \<inter> \<sigma> r = {}"
        using \<open>(\<exists>s b. Some s = Some a \<oplus> Some r \<and> s << b \<and> b \<in> A) \<and> ver Pr {a} (stmt.If s1 s2) \<and> set (modif (stmt.If s1 s2)) \<inter> \<sigma> r = {}\<close> ver_if by auto
      ultimately have "sem Pr ({ar}) s1 >> sem Pr {a} s1 \<oplus>\<oplus> {r}" using asm assms framing.simps[of Pr A s1]
        by (smt \<open>\<exists>b. Some ar = Some a \<oplus> Some r \<and> ar << b \<and> b \<in> A\<close> simple_set_add)
      moreover have "sem Pr {a} s1 >> sem Pr {a} (stmt.If s1 s2)" 
        using asm bigger_if_ver by blast
      ultimately have "sem Pr ({a} \<oplus>\<oplus> {r}) s1 >> sem Pr {a} (stmt.If s1 s2) \<oplus>\<oplus> {r}"
        using \<open>\<exists>b. Some ar = Some a \<oplus> Some r \<and> ar << b \<and> b \<in> A\<close> \<open>ver Pr {a} s1 \<and> set (modif s1) \<inter> \<sigma> r = {}\<close> assms(1) bigger_set_trans framing.simps plus_and_bigger_set by blast
      then show ?thesis
        using True bigger_set_def by blast
    next
      case False
      moreover have "sem Pr ({a} \<oplus>\<oplus> {r}) (stmt.If s1 s2) = sem Pr ({a} \<oplus>\<oplus> {r}) s1 \<union> sem Pr ({a} \<oplus>\<oplus> {r}) s2" using sem_if
        using \<open>ver Pr ({a} \<oplus>\<oplus> {r}) (stmt.If s1 s2)\<close> by blast
      then have "y \<in> sem Pr ({a} \<oplus>\<oplus> {r}) s2"
        using \<open>y \<in> sem Pr ({a} \<oplus>\<oplus> {r}) (stmt.If s1 s2)\<close> calculation by blast
      moreover have "ver Pr {a} s2 \<and> set (modif s2) \<inter> \<sigma> r = {}"
        using \<open>(\<exists>s b. Some s = Some a \<oplus> Some r \<and> s << b \<and> b \<in> A) \<and> ver Pr {a} (stmt.If s1 s2) \<and> set (modif (stmt.If s1 s2)) \<inter> \<sigma> r = {}\<close> ver_if by auto
      ultimately have "sem Pr ({ar}) s2 >> sem Pr {a} s2 \<oplus>\<oplus> {r}" using asm assms framing.simps[of Pr A s2]
        by (smt \<open>\<exists>b. Some ar = Some a \<oplus> Some r \<and> ar << b \<and> b \<in> A\<close> simple_set_add)
      moreover have "sem Pr {a} s2 >> sem Pr {a} (stmt.If s1 s2)" 
        using asm bigger_if_ver by blast
      ultimately have "sem Pr ({a} \<oplus>\<oplus> {r}) s2 >> sem Pr {a} (stmt.If s1 s2) \<oplus>\<oplus> {r}"
        using \<open>\<exists>b. Some ar = Some a \<oplus> Some r \<and> ar << b \<and> b \<in> A\<close> \<open>ver Pr {a} s2 \<and> set (modif s2) \<inter> \<sigma> r = {}\<close> assms(2) bigger_set_trans framing.simps plus_and_bigger_set by blast
      then show ?thesis
        using \<open>y \<in> sem Pr ({a} \<oplus>\<oplus> {r}) s2\<close> bigger_set_def by blast
    qed
  qed
qed

lemma framingMonoI:
  assumes "\<And>a r ar. Some ar = Some a \<oplus> Some r \<and> (\<exists>b. ar << b \<and> b \<in> A) \<and> ver Pr {a} s \<Longrightarrow> ver Pr {ar} s \<and> sem Pr ({ar}) s >> sem Pr {a} s \<and> (set (modif s) \<inter> \<sigma> r = {} \<longrightarrow> 
sem Pr ({ar}) s >> sem Pr {a} s \<oplus>\<oplus> {r})"
  shows "framing Pr A s"
proof (rule framingI)
  show "mono Pr A s"
    by (meson assms local.monoI smaller_def)
  fix a r assume "(\<exists>s b. Some s = Some a \<oplus> Some r \<and> s << b \<and> b \<in> A) \<and> ver Pr {a} s \<and> set (modif s) \<inter> \<sigma> r = {}"
  then show "sem Pr ({a} \<oplus>\<oplus> {r}) s >> sem Pr {a} s \<oplus>\<oplus> {r}"
    using assms simple_set_add by fastforce
qed

(*
definition smaller_pointwise :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "smaller_pointwise A B \<longleftrightarrow> (\<forall>a \<in> A. \<exists>b \<in> B. a << b)"
*)

lemma verBiggerI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> ver Pr {x} s \<and> sem Pr {x} s >> B"
  shows "ver Pr A s \<and> sem Pr A s >> B"
  by (meson assms biggerSingletonI bigger_set_forall elem_sem v_singleton)

lemma mono_comp:
  assumes "smono Pr A s1"
      and "smono Pr B s2"
      and "\<And>x y. \<exists>a\<in>A. x << a \<and> y \<in> sem Pr {x} s1 \<and> ver Pr {x} s1 \<Longrightarrow> \<exists>z\<in>B. y << z"
    shows "mono Pr A (s1 ; s2)"
proof (rule monoI)
  fix a b assume asm: "b << a \<and> ver Pr {b} (s1 ; s2) \<and> (\<exists>x\<in>A. a << x)"
  then have "ver Pr {a} s1 \<and> sem Pr {a} s1 >> sem Pr {b} s1" 
    by (meson assms(1) smonoOut_singleton smono_def ssafeMono_singleton ver_seq)
  moreover have "\<And>x. x \<in> sem Pr {a} s1 \<Longrightarrow> ver Pr {x} s2 \<and> sem Pr {x} s2 >> sem Pr (sem Pr {b} s1) s2"
  proof -
    fix y assume asm2: "y \<in> sem Pr {a} s1"
    then obtain z where "z \<in> B" "y << z" using assms(3) 
      using asm 
      using calculation by blast
    moreover obtain x where "x << y" "x \<in> sem Pr {b} s1" 
      using \<open>ver Pr {a} s1 \<and> sem Pr {a} s1 >> sem Pr {b} s1\<close> asm2 bigger_set_def by blast
    moreover have "ver Pr {x} s2" 
      using asm calculation(4) ver_def ver_seq by force
    ultimately have "ver Pr {y} s2 \<and> sem Pr {y} s2 >> sem Pr {x} s2" 
      by (meson assms(2) smonoOut_singleton smono_def ssafeMono_singleton)
    then show "ver Pr {y} s2 \<and> sem Pr {y} s2 >> sem Pr (sem Pr {b} s1) s2" using assms(2)
      by (metis \<open>x \<in> sem Pr {b} s1\<close> bigger_set_singleton singletonD)
  qed
  ultimately show "ver Pr {a} (s1 ; s2) \<and> sem Pr {a} (s1 ; s2) >> sem Pr {b} (s1 ; s2)"
    by (metis asm sem_seq_single verBiggerI ver_seq_single)
qed

lemma framing_comp:
  assumes "framing Pr A s1"
      and "framing Pr B s2"
      and "\<forall>x \<in> sem_ver Pr (fill_set A) s1. \<exists>y\<in>B. x << y"
    shows "framing Pr A (s1 ; s2)"
proof (rule framingMonoI)
  fix a r ar assume asm: "Some ar = Some a \<oplus> Some r \<and> (\<exists>b. ar << b \<and> b \<in> A) \<and> ver Pr {a} (s1 ; s2)"
  then obtain b where "ar << b" "b \<in> A" by blast
  moreover have "smono Pr A s1" 
    using assms(1) framing.simps by blast
  moreover have "a << ar" using asm 
    using smaller_def by blast
  ultimately have "ver Pr {ar} s1 \<and> sem Pr {ar} s1 >> sem Pr {a} s1" using ssafeMono_def smonoOut_def
    by (smt asm smonoOut_singleton smono_def ssafeMono_singleton ver_seq)
  then have "(set (modif (s1 ; s2)) \<inter> \<sigma> r = {} \<Longrightarrow> sem Pr {ar} s1 >> sem Pr {a} s1 \<oplus>\<oplus> {r})"
  proof -
    assume "set (modif (s1 ; s2)) \<inter> \<sigma> r = {}"
    then have "set (modif s1) \<inter> \<sigma> r = {}" by auto
    moreover have "{a} \<oplus>\<oplus> {r} = {ar}" using asm 
      by (simp add: simple_set_add)
    ultimately show "sem Pr {ar} s1 >> sem Pr {a} s1 \<oplus>\<oplus> {r}" using framing.simps[of Pr A s1] assms(1) asm
      using ver_seq_single by fastforce
  qed
  then have r1: "\<And>x. x \<in> sem Pr {ar} s1 \<Longrightarrow> ver Pr {x} s2 \<and> sem Pr {x} s2 >> sem Pr (sem Pr {a} s1) s2"
  proof -
    fix y assume asm2: "y \<in> sem Pr {ar} s1"
    then obtain x where "x \<in> sem Pr {a} s1" "x << y"
      using \<open>ver Pr {ar} s1 \<and> sem Pr {ar} s1 >> sem Pr {a} s1\<close> bigger_set_def by blast
    then have "ver Pr {x} s2"
      using asm v_singleton ver_seq by blast
    moreover have "\<exists>z \<in> B. y << z"
    proof -
      have "ar \<in> fill_set A"
        using \<open>ar << b\<close> \<open>b \<in> A\<close> elem_fill_set by blast
      then have "ar \<in> Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} s1) (fill_set A)" 
        by (simp add: \<open>ver Pr {ar} s1 \<and> sem Pr {ar} s1 >> sem Pr {a} s1\<close>)
      then have "y \<in> sem_ver Pr (fill_set A) s1" using sem_ver_def fill_set_def asm2 
        by fastforce
      then show ?thesis using assms(3) by blast
    qed
    then obtain z where "z \<in> B" "y << z" by blast
    ultimately have "ver Pr {y} s2"
      by (meson \<open>x << y\<close> assms(2) framing.simps smono_def ssafeMono_singleton)
    then have "sem Pr {y} s2 >> sem Pr {y} s2"
      by (simp add: subset_smaller)
    then show "ver Pr {y} s2 \<and> sem Pr {y} s2 >> sem Pr (sem Pr {a} s1) s2"
      by (metis (no_types, lifting) \<open>ver Pr {x} s2\<close> \<open>ver Pr {y} s2\<close> \<open>x << y\<close> \<open>x \<in> sem Pr {a} s1\<close> \<open>y << z\<close> \<open>z \<in> B\<close> assms(2) bigger_set_singleton framing.simps singletonD smonoOut_singleton smono_def)
  qed

  then have "ver Pr {ar} (s1 ; s2)"
    by (meson \<open>ver Pr {ar} s1 \<and> sem Pr {ar} s1 >> sem Pr {a} s1\<close> v_singleton ver_seq)
  have "sem Pr {ar} (s1 ; s2) >> sem Pr (sem Pr {a} s1) s2"
  proof (rule greaterI)
    fix y assume "y \<in> sem Pr {ar} (s1 ; s2)"
    then obtain x where "x \<in> sem Pr {ar} s1" "y \<in> sem Pr {x} s2"
      using \<open>ver Pr {ar} (s1 ; s2)\<close> sem_seq_single by auto
    then have "sem Pr {x} s2 >> sem Pr (sem Pr {a} s1) s2" using r1 by simp
    then show "\<exists>x\<in>sem Pr (sem Pr {a} s1) s2. x << y"
      using \<open>y \<in> sem Pr {x} s2\<close> bigger_set_def by blast
  qed
  moreover have "\<And>x. set (modif (s1 ; s2)) \<inter> \<sigma> r = {} \<and> x \<in> sem Pr {ar} s1 \<Longrightarrow> sem Pr {x} s2 >> sem Pr {a} (s1 ; s2) \<oplus>\<oplus> {r}"
  proof -
    fix y assume asm2: "set (modif (s1 ; s2)) \<inter> \<sigma> r = {} \<and> y \<in> sem Pr {ar} s1"
    then obtain x where "x \<in> sem Pr {a} s1 \<oplus>\<oplus> {r}" "x << y" 
      using \<open>set (modif (s1 ; s2)) \<inter> \<sigma> r = {} \<Longrightarrow> sem Pr {ar} s1 >> sem Pr {a} s1 \<oplus>\<oplus> {r}\<close> bigger_set_def by auto
    then obtain xx where "Some x = Some xx \<oplus> Some r" "xx \<in> sem Pr {a} s1" 
      using elem_add_set by auto
    moreover have "\<exists>z \<in> B. y << z"
    proof -
      have "ar \<in> fill_set A"
        using \<open>ar << b\<close> \<open>b \<in> A\<close> elem_fill_set by blast
      then have "ar \<in> Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} s1) (fill_set A)" 
        by (simp add: \<open>ver Pr {ar} s1 \<and> sem Pr {ar} s1 >> sem Pr {a} s1\<close>)
      then have "y \<in> sem_ver Pr (fill_set A) s1" using sem_ver_def fill_set_def asm2
        by force
      then show ?thesis using assms(3) by blast
    qed
    then obtain z where "z \<in> B" "y << z" by blast
    then have "x << z" 
      using \<open>x << y\<close> smaller_trans by blast
    moreover have "set (modif s2) \<inter> \<sigma> r = {}" using asm2 by auto
    moreover have "ver Pr {xx} s2"
      using asm calculation(2) v_singleton ver_seq by blast
    ultimately have "sem Pr ({xx} \<oplus>\<oplus> {r}) s2 >> sem Pr {xx} s2 \<oplus>\<oplus> {r}"
      using framing.simps[of Pr B s2]
      using \<open>z \<in> B\<close> assms(2) by blast
    moreover have "sem Pr {y} s2 >> sem Pr {x} s2"
    proof -
      have "mono Pr B s2" 
        using assms(2) framing.simps mono_smono by blast
      moreover have "ver Pr {x} s2" 
        by (meson \<open>Some x = Some xx \<oplus> Some r\<close> \<open>ver Pr {xx} s2\<close> \<open>x << z\<close> \<open>z \<in> B\<close> calculation mono_smono smaller_def smono_def ssafeMono_singleton)
      ultimately show ?thesis using smonoOut_def[of Pr B s2] 
        using \<open>x << y\<close> \<open>y << z\<close> \<open>z \<in> B\<close> mono_smono smonoOut_singleton smono_def by blast
    qed
    moreover have "{x} = {xx} \<oplus>\<oplus> {r}"
      using \<open>Some x = Some xx \<oplus> Some r\<close> simple_set_add by auto
    ultimately have "sem Pr {y} s2 >> sem Pr {xx} s2 \<oplus>\<oplus> {r}" 
      using bigger_set_trans
      by presburger
    moreover have "sem Pr {xx} s2 >> sem Pr {a} (s1 ; s2)" 
      by (metis \<open>xx \<in> sem Pr {a} s1\<close> add_sets_neutral asm bigger_set_singleton rel_bigger_add_set sem_seq singletonD)
    ultimately show "sem Pr {y} s2 >> sem Pr {a} (s1 ; s2) \<oplus>\<oplus> {r}" 
      by (meson bigger_set_trans bigger_sets_sum subset_refl subset_smaller)
  qed

  ultimately have "(set (modif (s1 ; s2)) \<inter> \<sigma> r = {} \<longrightarrow> sem Pr {ar} (s1 ; s2) >> sem Pr {a} (s1 ; s2) \<oplus>\<oplus> {r})"
    by (smt \<open>ver Pr {ar} (s1 ; s2)\<close> bigger_set_forall elem_sem sem_seq)
  then show "ver Pr {ar} (s1 ; s2) \<and> sem Pr {ar} (s1 ; s2) >> sem Pr {a} (s1 ; s2) \<and> (set (modif (s1 ; s2)) \<inter> \<sigma> r = {} \<longrightarrow> sem Pr {ar} (s1 ; s2) >> sem Pr {a} (s1 ; s2) \<oplus>\<oplus> {r})"
    using \<open>sem Pr {ar} (s1 ; s2) >> sem Pr (sem Pr {a} s1) s2\<close> \<open>ver Pr {ar} (s1 ; s2)\<close> asm sem_seq_single by auto
qed

lemma h_comp_bigger_set:
  assumes "set V \<subseteq> set V'"
  shows "h_comp x V' << h_comp x V"
proof -
  have "h_comp_some x V' << h_comp_some x V"
    by (metis Diff_mono assms h_comp_some_exists pure_is_exactly_store subset_refl)
  then show ?thesis 
    by (metis associative h_comp_some_sum smaller_def)
qed

lemma framing_inlined_loop:
  "SC Pr n A l (While b I s) \<Longrightarrow> framing Pr A (inline Pr n l (While b I s))"
proof (induction n arbitrary: A l)
  case 0
  then show ?case
  proof -
    assume "SC Pr 0 A l (While b I s)"
    then have "mono Pr A (Assume (lnot b))"
      by (simp add: mono_smono)
    then show "framing Pr A (inline Pr 0 l (While b I s))"
      using assume_mono_framing by auto
  qed
next
  case (Suc n)
  then have "inlinable_SC Pr (Suc n) A l (While b I s)" by simp
  then have asm1: "wfm Pr b \<and> framing Pr (f A b) (inline Pr n l s) \<and>
  SC Pr n (f A b) l s \<and> SC Pr n (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) (While b I s)"
    using inlinable_SC.simps(2) by blast

  let ?s = "inline Pr n l s"
  let ?w = "inline Pr n (l @ read (inline Pr n l s)) (While b I s)"
  have "inline Pr (Suc n) l (While b I s) = If (Assume b ; ?s ; ?w) (Assume (lnot b))" by simp

  moreover have "framing Pr A (Assume b ; ?s ; ?w)"
  proof -
    have "mono Pr A (Assume b)" using wfm_def asm1
      using mono_smono by blast
    then have "framing Pr A (Assume b)"
      using assume_mono_framing by blast
    moreover have "framing Pr (f A b) ?s" using asm1 by simp
    moreover have "\<And>x. x \<in> sem_ver Pr (fill_set A) (Assume b) \<Longrightarrow> \<exists>y\<in>f A b. x << y"
    proof -
      fix x assume asm2: "x \<in> sem_ver Pr (fill_set A) (Assume b)"
      then have r: "x \<in> fill_set A \<and> x \<in> sem Pr {x} (Assume b) \<and> ver Pr {x} (Assume b)"
        by (smt elem_sem f_inclusion insert_not_empty member_filter mk_disjoint_insert sem_assume_filter sem_ver_def singletonD subset_singletonD)
      then obtain y where "y \<in> A" "x << y" 
        using elem_fill_set by blast
      then have "ver Pr {y} (Assume b)" 
        using r calculation(1) framing.simps smaller_refl smono_def ssafeMono_singleton by blast
      moreover have "mono Pr A (Assume (lnot b))" using asm1 wfm_def
        using mono_smono by blast
      moreover have "lnot b x = Some False" using r lnot_def 
        using if_assume_then_true lnot_false_true(1) by fastforce
      ultimately have "lnot b y = Some False" 
        by (metis \<open>x << y\<close> \<open>y \<in> A\<close> assume_mono_same_b option.distinct(1) smaller_refl)
      then have "y \<in> f A b" using f_def \<open>y \<in> A\<close> lnot_def 
        by (simp add: lnot_false_true(1))
      then show "\<exists>y\<in>f A b. x << y" 
        using \<open>x << y\<close> by blast
    qed
    ultimately have "framing Pr A (Assume b ; ?s)" 
      using framing_comp by blast
    moreover have "framing Pr (sem_ver Pr (fill_set (f A b)) ?s) ?w"
      using Suc.IH asm1 by blast
    moreover have "\<And>x. x \<in> sem_ver Pr (fill_set A) (Assume b ; inline Pr n l s) \<Longrightarrow> \<exists>y\<in>sem_ver Pr (fill_set (f A b)) (inline Pr n l s). x << y"
    proof -
      fix x assume "x \<in> sem_ver Pr (fill_set A) (Assume b ; ?s)"
      then obtain xx where "xx \<in> fill_set A" "x \<in> sem Pr {xx} (Assume b ; ?s)" "ver Pr {xx} (Assume b ; ?s)" using sem_ver_def by auto
      then have "b xx = Some True" 
        by (metis empty_set_goes_empty equals0D semantics.simps(2) singleton_semantics ver_assume ver_seq_single well_defined_assert_def)
      then have "xx \<in> fill_set (f A b)"
      proof -
        obtain a where "a \<in> A" "xx << a"
          using \<open>xx \<in> fill_set A\<close> elem_fill_set by auto
        moreover have "mono Pr A (Assume (lnot b))" using asm1
          using mono_smono wfm_def by blast
        moreover have "lnot b xx =  Some False" 
          by (meson \<open>b xx = Some True\<close> lnot_false_true(1))
        ultimately have "lnot b a = Some False" 
          by (metis assume_mono_same_b option.distinct(1) smaller_refl)
        then have "a \<in> f A b" using lnot_def lnot_false_true f_def 
          by (simp add: \<open>\<And>x b. (b x = Some True) = (lnot b x = Some False)\<close> \<open>a \<in> A\<close>)
        then show ?thesis 
          using \<open>xx << a\<close> elem_fill_set by blast
      qed
      moreover have "x \<in> sem Pr {xx} ?s \<and> ver Pr {xx} ?s"  
        by (metis \<open>b xx = Some True\<close> \<open>ver Pr {xx} (Assume b ; inline Pr n l s)\<close> \<open>x \<in> sem Pr {xx} (Assume b ; inline Pr n l s)\<close> sem_assume_true sem_seq ver_assume ver_seq well_defined_assert_def)
      ultimately have "xx \<in> (Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} (inline Pr n l s)) (fill_set (f A b)))" by simp
      then have "x \<in> sem_ver Pr (fill_set (f A b)) ?s" using sem_ver_def[of Pr "fill_set (f A b)" ?s] 
        using \<open>x \<in> sem Pr {xx} (inline Pr n l s) \<and> ver Pr {xx} (inline Pr n l s)\<close> by auto
      then show "\<exists>y\<in>sem_ver Pr (fill_set (f A b)) (inline Pr n l s). x << y" 
        using smaller_refl by blast
    qed
    ultimately show ?thesis 
      using framing_comp by blast
  qed
  ultimately show ?case
    by (metis SC.elims(2) Suc.prems assume_mono_framing framing_if inlinable.simps(2) inlinable_SC.simps(2) mono_smono wfm_def)
qed

definition h_comp_modif_prop :: "('a, 'b, 'c) program \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "h_comp_modif_prop Pr s \<longleftrightarrow> (\<forall>x. ver Pr {x} s \<and> wf_stmt Pr s \<longrightarrow> sem Pr {x} s >> {h_comp |x| (modif s)})"

lemma h_comp_modif_prop_inhale:
  "h_comp_modif_prop Pr (Inhale I)"
  using associative commutative core_properties(1) core_properties(2) h_comp_sum int_squared_inhale_for_sets pure_set_add_smaller pure_smaller_ok s_core_def simple_set_add wf_stmt.simps(5)
  h_comp_modif_prop_def by smt

lemma h_comp_modif_prop_havoc:
  "h_comp_modif_prop Pr (Havoc V)"
  by (smt h_comp_modif_prop_def core_properties(1) core_properties(2) h_comp_add_single modif.simps(9) pure_set_add_smaller pure_smaller_ok sem_havoc set_add_asso simple_set_add simple_set_add_comm)

lemma h_comp_modif_prop_exhale:
  "h_comp_modif_prop Pr (Exhale I)"
  by (smt h_comp_modif_prop_def bigger_set_def bigger_set_trans core_properties(1) exhale_sem_bigger_core_bigger h_comp_smaller pure_set_add_smaller pure_smaller_ok simple_set_add singletonI smaller_pure supported_intui_exhale wf_stmt.simps(6))

lemma h_comp_modif_prop_assume:
  "h_comp_modif_prop Pr (Assume b)"
  by (smt h_comp_modif_prop_def core_properties(2) h_comp_smaller semantics.simps(2) singletonD singletonI singleton_semantics smaller_trans strongerI subset_singleton_iff subset_smaller ver_assume well_defined_assert_def)

lemma h_comp_modif_prop_seq:
  assumes "h_comp_modif_prop Pr s1"
      and "h_comp_modif_prop Pr s2"
    shows "h_comp_modif_prop Pr (s1 ; s2)"
proof -
  have "\<And>x. ver Pr {x} (s1 ; s2) \<and> wf_stmt Pr (s1 ; s2) \<Longrightarrow> sem Pr {x} (s1 ; s2) >> {h_comp |x| (modif (s1 ; s2))}"
  proof -
    fix x assume asm1: "ver Pr {x} (s1 ; s2) \<and> wf_stmt Pr (s1 ; s2)"
    then have "ver Pr {x} s1 \<and> wf_stmt Pr s1"  by (simp add: ver_seq)
    then have "sem Pr {x} s1 >> {h_comp |x| (modif s1)}"
      using assms(1) h_comp_modif_prop_def by blast
    moreover have "h_comp |x| (modif (s1 ; s2)) << h_comp |x| (modif s1)"
      by (simp add: h_comp_bigger_set)
    ultimately have "sem Pr {x} s1 >> {h_comp |x| (modif (s1 ; s2))}"
      using bigger_set_def smaller_trans by force
    then have "\<And>y. y \<in> sem Pr {x} s1 \<Longrightarrow> sem Pr {y} s2 >> {h_comp |x| (modif (s1 ; s2))}"
    proof -
      fix y assume asm: "y \<in> sem Pr {x} s1"
      then have "h_comp |x| (modif (s1 ; s2)) << y" 
        using \<open>sem Pr {x} s1 >> {h_comp |x| (modif (s1 ; s2))}\<close> bigger_set_def by auto
      moreover have "ver Pr {y} s2 \<and> wf_stmt Pr s2" 
        by (meson asm1 asm v_singleton ver_seq wf_stmt.simps(1))
      then have "sem Pr {y} s2 >> {h_comp |y| (modif s2)}" 
        using assms(2) h_comp_modif_prop_def by simp
      moreover have "h_comp |h_comp |x| (modif (s1 ; s2))| (modif s2) << h_comp |y| (modif s2)"
        using calculation(1) h_comp_grows smaller_core_comp by blast
      moreover have "h_comp |h_comp |x| (modif (s1 ; s2))| (modif (s1 ; s2)) << h_comp |h_comp |x| (modif (s1 ; s2))| (modif s2)"
        by (simp add: h_comp_bigger_set)
      moreover have "h_comp |h_comp |x| (modif (s1 ; s2))| (modif (s1 ; s2)) = h_comp |x| (modif (s1 ; s2))" 
        by (metis Diff_disjoint core_properties(1) h_comp_not_here h_comp_smaller h_comp_store not_pure_core smaller_pure)
      ultimately show "sem Pr {y} s2 >> {h_comp |x| (modif (s1 ; s2))}" 
        using bigger_set_trans core_properties(1) h_comp_smaller h_comp_smaller_elem local.antisym not_pure_core rel_bigger_add_set smaller_pure
        by smt
    qed
    then show "sem Pr {x} (s1 ; s2) >> {h_comp |x| (modif (s1 ; s2))}" 
      by (metis (no_types, lifting) asm1 sem_seq v_singleton verBiggerI ver_seq)
  qed
  then show ?thesis using h_comp_modif_prop_def by simp
qed

lemma wf_program_aux_wf_method:
  assumes "wf_program_aux Pr l"
      and "get_method l m = Some mm"
    shows "wf_method Pr mm"
  using assms
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case 
    using wf_program_method_aux by blast
qed

lemma statement_doesnt_modif:
  "ver Pr {x} s \<and> wf_stmt Pr s \<and> wf_program Pr \<Longrightarrow> sem Pr {x} s >> {h_comp |x| (modif s)}"
proof (induction s arbitrary: x)
  case (Inhale x)
  then show ?case 
    by (smt associative commutative core_properties(1) core_properties(2) h_comp_sum int_squared_inhale_for_sets pure_set_add_smaller pure_smaller_ok s_core_def simple_set_add wf_stmt.simps(5))
next
  case (Assume x)
  then show ?case 
    by (smt core_properties(2) h_comp_smaller semantics.simps(2) singletonD singletonI singleton_semantics smaller_trans strongerI subset_singleton_iff subset_smaller ver_assume well_defined_assert_def)
next
  case (Exhale x)
  then show ?case 
    by (smt bigger_set_def bigger_set_trans core_properties(1) exhale_sem_bigger_core_bigger h_comp_smaller pure_set_add_smaller pure_smaller_ok simple_set_add singletonI smaller_pure supported_intui_exhale wf_stmt.simps(6))
next
  case Skip
  then show ?case
    by (metis core_properties(2) h_comp_smaller sem_skip singletonD singletonI smaller_trans strongerI)
next
  case (Seq s1 s2)
  then have "ver Pr {x} s1 \<and> wf_stmt Pr s1" 
    by (simp add: ver_seq)
  then have "sem Pr {x} s1 >> {h_comp |x| (modif s1)}"
    using Seq.IH(1) Seq.prems by simp
  moreover have "h_comp |x| (modif (s1 ; s2)) << h_comp |x| (modif s1)"
    by (simp add: h_comp_bigger_set)
  ultimately have "sem Pr {x} s1 >> {h_comp |x| (modif (s1 ; s2))}"
    using bigger_set_def smaller_trans by force
  then have "\<And>y. y \<in> sem Pr {x} s1 \<Longrightarrow> sem Pr {y} s2 >> {h_comp |x| (modif (s1 ; s2))}"
  proof -
    fix y assume asm: "y \<in> sem Pr {x} s1"
    then have "h_comp |x| (modif (s1 ; s2)) << y" 
      using \<open>sem Pr {x} s1 >> {h_comp |x| (modif (s1 ; s2))}\<close> bigger_set_def by auto
    moreover have "ver Pr {y} s2 \<and> wf_stmt Pr s2" 
      by (meson Seq.prems asm v_singleton ver_seq wf_stmt.simps(1))
    then have "sem Pr {y} s2 >> {h_comp |y| (modif s2)}" 
      using Seq.IH(2) Seq.prems by simp
    moreover have "h_comp |h_comp |x| (modif (s1 ; s2))| (modif s2) << h_comp |y| (modif s2)"
      using calculation(1) h_comp_grows smaller_core_comp by blast
    moreover have "h_comp |h_comp |x| (modif (s1 ; s2))| (modif (s1 ; s2)) << h_comp |h_comp |x| (modif (s1 ; s2))| (modif s2)"
      by (simp add: h_comp_bigger_set)
    moreover have "h_comp |h_comp |x| (modif (s1 ; s2))| (modif (s1 ; s2)) = h_comp |x| (modif (s1 ; s2))" 
      by (metis Diff_disjoint core_properties(1) h_comp_not_here h_comp_smaller h_comp_store not_pure_core smaller_pure)
    ultimately show "sem Pr {y} s2 >> {h_comp |x| (modif (s1 ; s2))}" 
      by (smt bigger_set_trans core_properties(1) h_comp_smaller h_comp_smaller_elem local.antisym not_pure_core rel_bigger_add_set smaller_pure)
  qed
  then show ?case 
    by (metis (no_types, lifting) Seq.prems sem_seq v_singleton verBiggerI ver_seq)
next
  case (If s1 s2)
  have "\<And>y. y \<in> sem Pr {x} (stmt.If s1 s2) \<Longrightarrow> {y} >> {h_comp |x| (modif (If s1 s2))}"
  proof -
    fix y assume asm: "y \<in> sem Pr {x} (stmt.If s1 s2)"
    then show "{y} >> {h_comp |x| (modif (If s1 s2))}"
    proof (cases "y \<in> sem Pr {x} s1")
      case True
      have "sem Pr {x} s1 >> {h_comp |x| (modif s1)}" using If.IH(1)[of x] 
        using If.prems ver_if wf_stmt.simps(2) by blast
      moreover have "h_comp |x| (modif (If s1 s2)) << h_comp |x| (modif s1)"
        using h_comp_bigger_set by simp
      ultimately show ?thesis 
        using True bigger_set_def smaller_trans by force
    next
      case False
      then have "y \<in> sem Pr {x} s2" using sem_if asm If.prems by blast
      moreover have "sem Pr {x} s2 >> {h_comp |x| (modif s2)}" using If.IH(2)[of x] 
        using If.prems ver_if wf_stmt.simps(2) by blast
      moreover have "h_comp |x| (modif (If s1 s2)) << h_comp |x| (modif s2)"
        using h_comp_bigger_set by simp
      ultimately show ?thesis
        using bigger_set_def smaller_trans by force
    qed
  qed
  then show ?case 
    using biggerSingletonI by blast
next
  case (Var x)
  then show ?case 
    by (smt core_properties(1) core_properties(2) h_comp_not_here h_comp_sum_set_smaller_pure modif.simps(8) pure_set_add_smaller sem_var set_add_asso simple_set_add_comm ver_var)
next
  case (Havoc x)
  then show ?case 
    by (smt core_properties(1) core_properties(2) h_comp_add_single modif.simps(9) pure_set_add_smaller pure_smaller_ok sem_havoc set_add_asso simple_set_add simple_set_add_comm)
next
  case (MethodCall y m xx)
  then show ?case
  proof (cases "get_method Pr m")
    case None
    then show ?thesis 
      using MethodCall.prems by auto
  next
    case (Some a)
    then obtain args rets P Q s where asm: "a = (m, args, rets, P, Q, s)"
      by (metis fst_conv get_method_same_name old.prod.exhaust option.distinct(1) option.sel)
    let ?P = "rename_pred P (args @ rets, xx @ y, [], [])"
    let ?Q = "rename_pred Q (args @ rets, xx @ y, [], [])"
    have "ver Pr {x} (MethodCall y m xx)" 
      using MethodCall.prems by blast
    moreover have "wf_stmt Pr (MethodCall y m xx)" using MethodCall.prems by simp
    moreover have "get_method Pr m = Some (m, args, rets, P, Q, s)" 
      by (simp add: Some \<open>a = (m, args, rets, P, Q, s)\<close>)
    ultimately have "sem Pr {x} (MethodCall y m xx) = sem Pr {x} (Exhale ?P ; Havoc y ; Inhale ?Q)"
      using sem_method_real[of Pr m args rets P Q s x y xx] by metis
    then have "h_comp_modif_prop Pr (Inhale ?Q)" 
      using h_comp_modif_prop_inhale by blast
    then have "h_comp_modif_prop Pr (Havoc y ; Inhale ?Q)"
      using h_comp_modif_prop_havoc h_comp_modif_prop_seq by blast
    then have "h_comp_modif_prop Pr (Exhale ?P ; Havoc y ; Inhale ?Q)" 
      by (simp add: h_comp_modif_prop_exhale h_comp_modif_prop_havoc h_comp_modif_prop_inhale h_comp_modif_prop_seq)
    moreover have "ver Pr {x} (Exhale ?P ; Havoc y ; Inhale ?Q)" 
      using \<open>get_method Pr m = Some (m, args, rets, P, Q, s)\<close> \<open>ver Pr {x} (MethodCall y m xx)\<close> ver_method_real by blast
    moreover have "wf_stmt Pr (Exhale ?P ; Havoc y ; Inhale ?Q)"
    proof -
      have "wf_program_aux Pr Pr" using MethodCall.prems 
        using wf_program.elims(1) by blast
      then have wf_meth: "wf_method Pr (m, args, rets, P, Q, s)" 
        using \<open>get_method Pr m = Some (m, args, rets, P, Q, s)\<close> wf_program_method_aux by blast
      moreover have "wf_renaming (args @ rets, xx @ y, [], [])" using wf_meth_stmt_wf_renaming[of Pr y m xx args rets P Q s]
        MethodCall wf_meth \<open>get_method Pr m = Some (m, args, rets, P, Q, s)\<close>
        by simp
      moreover have "wf_assert ?P" 
        using calculation(2) same_wf_rename wf_meth wf_method.simps by blast
      moreover have "wf_assert ?Q" 
        using calculation(2) same_wf_rename wf_meth wf_method.simps by blast
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis 
      using \<open>sem Pr {x} (MethodCall y m xx) = sem Pr {x} (Exhale (rename_pred P (args @ rets, xx @ y, [], [])) ; Havoc y ; Inhale (rename_pred Q (args @ rets, xx @ y, [], [])))\<close> h_comp_modif_prop_def by auto
  qed
next
  case (While b I s)
  have "sem Pr {x} (While b I s) = sem Pr {x} (Exhale I ; Havoc (filter_sigma x (modif s)) ; Inhale I ; Assume (lnot b))"
    using sem_loop While by blast
  moreover have "h_comp_modif_prop Pr (Exhale I ; Havoc (filter_sigma x (modif s)) ; Inhale I ; Assume (lnot b))"
    by (simp add: h_comp_modif_prop_assume h_comp_modif_prop_exhale h_comp_modif_prop_havoc h_comp_modif_prop_inhale h_comp_modif_prop_seq)
  moreover have "wf_stmt Pr (Exhale I ; Havoc (filter_sigma x (modif s)) ; Inhale I ; Assume (lnot b))"
    using While.prems by auto
  moreover have "ver Pr {x} (Exhale I ; Havoc (filter_sigma x (modif s)) ; Inhale I ; Assume (lnot b))"
    using While.prems ver_loop by blast
  ultimately have "sem Pr {x} (Exhale I ; Havoc (filter_sigma x (modif s)) ; Inhale I ; Assume (lnot b)) >> {h_comp |x| (modif ((Exhale I ; Havoc (filter_sigma x (modif s)) ; Inhale I ; Assume (lnot b))))}"
    using h_comp_modif_prop_def by blast
  moreover have "set (modif ((Exhale I ; Havoc (filter_sigma x (modif s)) ; Inhale I ; Assume (lnot b)))) \<subseteq> set (modif (While b I s))" 
    by (simp add: filter_sigma_included)
  ultimately show ?case  
    by (smt \<open>sem Pr {x} (While b I s) = sem Pr {x} (Exhale I ; Havoc (filter_sigma x (modif s)) ; Inhale I ; Assume (lnot b))\<close> bigger_set_def h_comp_bigger_set singletonD singletonI smaller_trans)
next
  case (Other other)
  then show ?case using no_modif_other 
    by (simp add: ver_def)
qed

lemma filter_sigma_same:
  "\<sigma> a = \<sigma> b \<Longrightarrow> filter_sigma a V = filter_sigma b V"
proof (induction V)
  case Nil
  then show ?case 
    by (simp add: filter_sigma_def)
next
  case (Cons a V)
  then show ?case 
    by (simp add: filter_sigma_def)
qed

lemma fill_set_sem_ver:
  assumes "ver Pr {x} s"
      and "x << a"
      and "a \<in> A"
      and "y \<in> sem Pr {x} s"
    shows "y \<in> sem_ver Pr (fill_set A) s"
proof -
  have "x \<in> fill_set A" 
    using assms(2) assms(3) elem_fill_set by blast
  then have "x \<in> Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} s) (fill_set A)"
    by (simp add: assms(1))
  then show ?thesis using sem_ver_def sem.simps[of Pr "Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} s) (fill_set A)" s] 
    using assms(4) by auto
qed

lemma loop_inling_induct:
  assumes "SP Pr n (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) (While b I s)"
      and "SP Pr n (f A b) l s"
    shows "SP Pr (Suc n) A l (While b I s)"
proof (rule SP_I)

  let ?w = "While b I s"
  let ?w' = "inline Pr n (l @ read (inline Pr n l s)) (While b I s)"
  let ?s' = "inline Pr n l s"

  fix \<phi> \<phi>'
  assume asm: "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr (While b I s) \<and> SC Pr (Suc n) A l (While b I s)
  \<and> no_inter A l \<and> set (modif (While b I s)) \<subseteq> set l \<and> (\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} (While b I s)"
  then have asm_implied: "wfm Pr b \<and> framing Pr (f A b) (inline Pr n l s) \<and>
  SC Pr n (f A b) l s \<and> SC Pr n (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) (While b I s)"
    by simp
  moreover obtain \<phi>'' where \<phi>''_def: "\<phi>'' \<in> A" "\<phi>' << \<phi>''"
    using asm by blast
  then have "\<phi> << \<phi>''" using asm smaller_trans by blast
  moreover obtain "wf_stmt Pr s" "set (modif s) \<subseteq> set l" "wf_assert I" using asm by simp

  moreover have "inline Pr (Suc n) l (While b I s) = If (Assume b ; ?s' ; ?w') (Assume (lnot b))" by simp

  define V where "V = filter_sigma \<phi> (modif s)"


  then obtain "ver Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b))"
    "ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)"
    using asm ver_loop by metis
  then have "{\<phi>} >> Inh I"
    using calculation(5) supported_intui_exhale ver_seq by blast
  then obtain i r where "Some \<phi> = Some i \<oplus> Some r" "i \<in> Inh I"
    using bigger_set_def smaller_def by auto
  let ?r = "h_comp r V"
  have decompo: "Some \<phi> = Some i \<oplus> s_core \<phi> \<oplus> Some ?r"
    by (metis Diff_cancel \<open>Some \<phi> = Some i \<oplus> Some r\<close> associative commutative core_add exists_list_minus h_comp_not_here h_comp_sum inf_bot_left)

  then obtain i_phi where "Some i_phi = Some i \<oplus> s_core \<phi>"
    by (metis option.discI plus.elims)
  then obtain core_i_phi where "Some core_i_phi = s_core i \<oplus> s_core \<phi>"
    by (metis associative commutative h_comp_sum option.exhaust_sel plus.simps(2))
  moreover obtain core_i_phi_r where core_i_phi_r_def: "Some core_i_phi_r =  s_core i \<oplus> s_core \<phi> \<oplus> Some ?r" using decompo
    associative commutative h_comp_sum option.exhaust_sel plus.simps(2)
  proof -
    assume a1: "\<And>core_i_phi_r. Some core_i_phi_r = s_core i \<oplus> s_core \<phi> \<oplus> Some (h_comp r V) \<Longrightarrow> thesis"
    have "Some (h_comp r V) \<oplus> (s_core \<phi> \<oplus> s_core i) = None \<longrightarrow> (\<exists>a. Some a = Some (h_comp r V) \<oplus> (s_core \<phi> \<oplus> s_core i))"
      by (metis (no_types) associative commutative decompo h_comp_sum plus.simps(2))
    then show ?thesis
      using a1 commutative by auto
  qed

  define F where "F = {h_comp |\<phi>| V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I"

  have "ver Pr { |\<phi>| } (Havoc V) \<and> sem Pr { |\<phi>| } (Havoc V) = { h_comp |\<phi>| V} \<oplus>\<oplus> h V"
    using V_def filter_sigma_in store_pure ver_havoc by auto
  then have "ver Pr ({ h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) \<and> sem Pr ({ h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) = F" 
    using F_def \<open>ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)\<close> sem_inhale ver_inhale ver_seq_single by auto
  then have "ver Pr F (Assume b) \<and> sem Pr F (Assume b) = f F b"
    by (metis \<open>ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)\<close> \<open>ver Pr {|\<phi>|} (Havoc V) \<and> sem Pr {|\<phi>|} (Havoc V) = {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> sem_assume_filter sem_seq_single ver_seq_single)
  then have "ver Pr (f F b) s \<and> sem Pr (f F b) s >> Inh I"
    by (metis \<open>ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) \<and> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) = F\<close> \<open>ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)\<close> \<open>ver Pr {|\<phi>|} (Havoc V) \<and> sem Pr {|\<phi>|} (Havoc V) = {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> calculation(5) sem_seq_single supported_intui_exhale ver_seq_single)

  then have "ver Pr {i_phi} ?w \<and> sem Pr {i_phi} ?w >> f F (lnot b)"
  proof -
    have "|i_phi| = |\<phi>|"
    proof -
      have "|i_phi| << |\<phi>|" 
        by (metis \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>\<And>thesis. (\<And>i_phi. Some i_phi = Some i \<oplus> s_core \<phi> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> decompo smaller_core_comp smaller_def)
      moreover have "|\<phi>| << i_phi" 
        using \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>Some core_i_phi = s_core i \<oplus> s_core \<phi>\<close> \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> add_trans commutative core_add core_inv core_is_max_uni core_properties(1) core_properties(2) elem_fill_set empty_in_pure option.sel pure_reducibility pure_smaller_ok pure_u s_core_def smaller_def smaller_pure smaller_refl smaller_trans u_smaller
        by metis
      ultimately show ?thesis 
        by (metis core_inv local.antisym smaller_core_comp)
    qed
    moreover have "V = filter_sigma i_phi (modif s)"
    proof (induction "modif s")
      case Nil
      then show ?case 
        using V_def filter_sigma_def by auto
    next
      case (Cons a x)
      have "\<sigma> \<phi> = \<sigma> i_phi" 
        by (metis calculation store_pure)
      then show ?case
        using V_def filter_sigma_def by auto
    qed
    moreover have "ver Pr {i_phi} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) \<and> sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) >> f F (lnot b)"
    proof -
      have "ver Pr {i_phi} (Exhale I)"
      proof -
        have "{i_phi} >> {i}"
          by (metis \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> commutative_monoid.s_core_def commutative_monoid_axioms rel_bigger_add_set simple_set_add)
        then show ?thesis using asm
          using \<open>i \<in> Inh I\<close> bigger_set_def supported_intui_exhale by auto
      qed
      then have "{ |\<phi>| } >> sem Pr {i_phi} (Exhale I)"
        by (metis \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>i \<in> Inh I\<close> \<open>wf_assert I\<close> calculation(1) core_add core_inv s_core_def simple_sem_exhale subset_smaller)
      
      then have "ver Pr (sem Pr {i_phi} (Exhale I)) (Havoc V)"
        by (smt IntE V_def \<open>ver Pr {i_phi} (Exhale I)\<close> calculation(1) filter_sigma_in store_pure store_same_pred_supp_exhale subsetI v_singleton ver_havoc)
      moreover have "ver Pr { |\<phi>| } (Havoc V)" 
        using V_def filter_sigma_in store_pure ver_havoc by auto
      moreover have "smono Pr ({ |\<phi>| } \<union> sem Pr {i_phi} (Exhale I)) (Havoc V)"
        using havoc_smono by blast
      ultimately have "sem Pr { |\<phi>| } (Havoc V) >> sem Pr (sem Pr {i_phi} (Exhale I)) (Havoc V)"
         by (smt \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>i \<in> Inh I\<close> \<open>wf_assert I\<close> \<open>|i_phi| = |\<phi>|\<close> bigger_set_singleton core_add core_inv core_properties(2) h_v_add insert_subset rel_bigger_add_set s_core_def sem_havoc set_add_asso simple_sem_exhale singletonD)
       let ?A = "sem Pr { |\<phi>| } (Havoc V)"
       let ?B = "sem Pr (sem Pr {i_phi} (Exhale I)) (Havoc V)"
       have "ver Pr ?B (Inhale I) \<and> sem Pr ?B (Inhale I) >> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I)"
       proof -
         have "\<And>xx. xx \<in> ?B \<Longrightarrow> ver Pr {xx} (Inhale I) \<and> sem Pr {xx} (Inhale I) >> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I)"
         proof -
           fix xx assume "xx \<in> ?B"
           then obtain xxx where "xxx \<in> sem Pr {i_phi} (Exhale I)" "xx \<in> sem Pr {xxx} (Havoc V)"
             using elem_sem by blast
           then have "|\<phi>| = |xxx|"
           proof -
             obtain ii rr where "Some i_phi = Some ii \<oplus> Some rr" "Some xxx = s_core ii \<oplus> Some rr" "ii \<in> Inh I"
               using sem_exhale[of I i_phi Pr] asm \<open>xxx \<in> sem Pr {i_phi} (Exhale I)\<close>
               by (smt \<open>ver Pr {i_phi} (Exhale I)\<close> exhale_elem)
             then have "s_core i_phi = s_core ii \<oplus> s_core rr"
               using core_add by blast
             moreover have "s_core xxx = s_core ii \<oplus> s_core rr"
             proof -
               have "s_core |ii| = s_core ii"
                 using core_inv
                 by (simp add: s_core_def)
               then show ?thesis 
                 using \<open>Some xxx = s_core ii \<oplus> Some rr\<close> core_add s_core_def by auto
             qed
             ultimately show ?thesis
               by (metis (full_types) \<open>|i_phi| = |\<phi>|\<close> option.sel s_core_def)
           qed
           moreover have "ver Pr {xxx} (Havoc V)" 
             using \<open>ver Pr (sem Pr {i_phi} (Exhale I)) (Havoc V)\<close> \<open>xxx \<in> sem Pr {i_phi} (Exhale I)\<close> v_singleton by blast
           then obtain hv where "hv \<in> h V" "Some xx = Some (h_comp xxx V) \<oplus> Some hv"
             using sem_havoc[of Pr xxx V] 
             using \<open>xx \<in> sem Pr {xxx} (Havoc V)\<close> elem_add_set by auto
           then have "{xx} >> {h_comp |\<phi>| V} \<oplus>\<oplus> h V"
           proof -
             have "{h_comp xxx V} >> {h_comp |\<phi>| V}"
               using calculation core_properties(2) h_comp_grows strongerI by fastforce
             moreover have "{hv} >> h V" 
               by (simp add: \<open>hv \<in> h V\<close> subset_smaller)
             ultimately show ?thesis 
               using \<open>Some xx = Some (h_comp xxx V) \<oplus> Some hv\<close> bigger_sets_sum simple_set_add by fastforce
           qed
           moreover have "ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I)"
             using \<open>ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) \<and> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) = F\<close> by blast
           moreover have "mono Pr (({h_comp |\<phi>| V} \<oplus>\<oplus> h V) \<union> {xx}) (Inhale I)"
             by (simp add: \<open>wf_assert I\<close> inhale_smono mono_smono)
           ultimately have "ver Pr {xx} (Inhale I)"
             using DiffI \<open>wf_assert I\<close> emptyE insertI1 insert_iff simple_set_add_comm singleton_iff smaller_refl ssafeMono_def union_sum v_singleton ver_inhale_single wf_assert_monoIn(1)
             by smt
           then have "sem Pr {xx} (Inhale I) >> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I)"
             by (metis \<open>ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I)\<close> \<open>{xx} >> {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> plus_and_bigger_set sem_inhale ver_inhale)
           then show "ver Pr {xx} (Inhale I) \<and> sem Pr {xx} (Inhale I) >> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I)"
             using \<open>ver Pr {xx} (Inhale I)\<close> by blast
         qed
         then show ?thesis 
           by (meson bigger_set_forall elem_sem v_singleton)
       qed
       then have "ver Pr {i_phi} (Exhale I ; Havoc V ; Inhale I)" 
         using \<open>ver Pr (sem Pr {i_phi} (Exhale I)) (Havoc V)\<close> \<open>ver Pr {i_phi} (Exhale I)\<close> sem_seq ver_seq by presburger
       
       moreover have "sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I) >> sem Pr ({|\<phi>|}) (Havoc V ; Inhale I)"
         by (metis \<open>ver Pr (sem Pr (sem Pr {i_phi} (Exhale I)) (Havoc V)) (Inhale I) \<and> sem Pr (sem Pr (sem Pr {i_phi} (Exhale I)) (Havoc V)) (Inhale I) >> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I)\<close> \<open>ver Pr (sem Pr {i_phi} (Exhale I)) (Havoc V)\<close> \<open>ver Pr {i_phi} (Exhale I)\<close> \<open>ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)\<close> sem_havoc sem_seq_single ver_seq_single)
       then have "sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I) >> F"
         by (metis F_def \<open>ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)\<close> sem_havoc sem_inhale sem_seq_single ver_inhale ver_seq_single)
       moreover have ver_F: "ver Pr F (Assume (lnot b))" 
         by (metis \<open>ver Pr F (Assume b) \<and> sem Pr F (Assume b) = f F b\<close> lnot_def v_singleton ver_assume wfm_not_same)

       moreover have mono_as: "mono Pr (sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I)) (Assume (lnot b))" using asm_implied wfm_def 
         using mono_smono by blast

 (* Almost done: TODO: Use MONO (from WFM), is exhale i ; inhale i enough? *)
       ultimately have "ver Pr (sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I)) (Assume (lnot b))
   \<and> sem Pr (sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I)) (Assume (lnot b)) >> sem Pr F (Assume (lnot b))"
       proof -
         have "\<And>xx. xx \<in> sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I) \<Longrightarrow> ver Pr {xx} (Assume (lnot b)) \<and>
sem Pr {xx} (Assume (lnot b)) >> sem Pr F (Assume (lnot b))"
         proof -
           fix xx assume "xx \<in> sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I)"
           then have "{xx} >> F"
             using \<open>sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I) >> F\<close> bigger_set_forall by blast
           then have "ver Pr {xx} (Assume (lnot b))" using ver_F mono_as ssafeMono_def[of Pr _ "Assume (lnot b)"]
             by (smt \<open>sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I) >> F\<close> \<open>xx \<in> sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I)\<close> mono_smono smaller_refl smono_def v_singleton)
           then have "sem Pr {xx} (Assume (lnot b)) >> sem Pr F (Assume (lnot b))"
using ver_F mono_as 
             \<open>sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I) >> F\<close> \<open>xx \<in> sem Pr {i_phi} (Exhale I ; Havoc V ; Inhale I)\<close> mono_smono smaller_refl smono_def v_singleton
              using \<open>{xx} >> F\<close>
              by (smt bigger_set_def bigger_set_singleton smonoOut_singleton smono_singleton)
           then show "ver Pr {xx} (Assume (lnot b)) \<and> sem Pr {xx} (Assume (lnot b)) >> sem Pr F (Assume (lnot b))"
             using \<open>ver Pr {xx} (Assume (lnot b))\<close> by blast
         qed
         then show ?thesis
           by (meson bigger_set_forall elem_sem v_singleton)
       qed
       then show ?thesis
         by (metis \<open>ver Pr F (Assume (lnot b))\<close> \<open>ver Pr {i_phi} (Exhale I ; Havoc V ; Inhale I)\<close> sem_assume_filter sem_seq ver_seq)
     qed

    moreover have "ver Pr {i_phi} ?w"
      using \<open>ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)\<close> calculation(1) calculation(2) calculation(3) ver_loop by auto
    then show ?thesis
      using calculation(2) calculation(3) sem_loop by auto
  qed


  have "f (F \<oplus>\<oplus> {?r}) (lnot b) \<subseteq> sem Pr {\<phi>} ?w \<and> ver Pr (F \<oplus>\<oplus> {?r}) (Assume (lnot b))"
  proof -
    have "sem Pr {\<phi>} ?w = sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b))"
      using V_def \<open>ver Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b))\<close> \<open>ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)\<close> sem_loop ver_loop by blast
    then have "sem Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b)) \<subseteq> ... \<and> ver Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b))"
    proof -
      obtain core_phi_r where "Some core_phi_r = s_core \<phi> \<oplus> Some ?r"
        by (metis associative decompo option.exhaust_sel plus.elims)
      then have "Some \<phi> = Some i \<oplus> Some core_phi_r"
        by (simp add: associative decompo)
      then have "{the (s_core i \<oplus> Some core_phi_r)} \<subseteq> sem Pr {\<phi>} (Exhale I)"
        by (metis \<open>Some core_phi_r = s_core \<phi> \<oplus> Some (h_comp r V)\<close> \<open>i \<in> Inh I\<close> associative calculation(5) core_i_phi_r_def option.sel simple_sem_exhale)
      then have "{core_i_phi_r} \<subseteq> sem Pr {\<phi>} (Exhale I)"
        by (metis \<open>Some \<phi> = Some i \<oplus> Some core_phi_r\<close> \<open>Some core_phi_r = s_core \<phi> \<oplus> Some (h_comp r V)\<close> \<open>i \<in> Inh I\<close> associative calculation(5) core_i_phi_r_def simple_sem_exhale)
      moreover have "sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) = sem Pr (sem Pr {\<phi>} (Exhale I)) (Havoc V ; Inhale I ; Assume (lnot b))"
        by (smt \<open>ver Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b))\<close> sem_seq ver_seq)
      ultimately show ?thesis
        by (smt \<open>ver Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b))\<close> elem_sem insert_subset sem_seq subsetI v_singleton ver_seq)
    qed
    moreover have "sem Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b))
  = sem Pr ({h_comp core_i_phi_r V} \<oplus>\<oplus> h V) (Inhale I ; Assume (lnot b))"
      by (smt sem_havoc sem_seq ver_seq calculation(1))
    moreover have "... = sem Pr ({h_comp core_i_phi_r V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I) (Assume (lnot b))"
      by (smt \<open>sem Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b)) \<subseteq> sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) \<and> ver Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b))\<close> sem_havoc sem_inhale sem_seq ver_inhale ver_seq)
    moreover have "... = f ({h_comp core_i_phi_r V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I) (lnot b)"
      by (metis (no_types, lifting) \<open>sem Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b)) \<subseteq> sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) \<and> ver Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b))\<close> sem_assume_filter sem_havoc sem_inhale sem_seq_single ver_inhale ver_seq_single)
    ultimately have "f ({h_comp core_i_phi_r V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I) (lnot b) \<subseteq> sem Pr {\<phi>} ?w"
      using \<open>sem Pr {\<phi>} (While b I s) = sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b))\<close> by blast
    moreover have "{h_comp core_i_phi_r V} = {h_comp |\<phi>| V} \<oplus>\<oplus> {?r}"
    proof -
      have "Some (h_comp core_i_phi_r V) = Some (h_comp core_i_phi V) \<oplus> Some (h_comp ?r V)"
        using \<open>Some core_i_phi = s_core i \<oplus> s_core \<phi>\<close> core_i_phi_r_def h_comp_lin by presburger
      moreover have "core_i_phi = |\<phi>|"
        using \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>Some core_i_phi = s_core i \<oplus> s_core \<phi>\<close> commutative core_add core_inv core_properties(1) core_properties(2) partially_cancellative pure_smaller_ok s_core_def smaller_def smaller_trans
      proof -
        have f1: "Some |\<phi>| \<oplus> Some |i| = Some core_i_phi"
          by (simp add: \<open>Some core_i_phi = s_core i \<oplus> s_core \<phi>\<close> commutative s_core_def)
        have "\<exists>a. Some |\<phi>| = Some |i| \<oplus> Some a"
          using \<open>Some \<phi> = Some i \<oplus> Some r\<close> core_add s_core_def by auto
        then show ?thesis
          using f1 by (metis (no_types) \<open>\<And>\<phi>. pure |\<phi>|\<close> option.inject pure_smaller_ok smaller_def)
      qed
      moreover have "h_comp ?r V = ?r"
        by (simp add: h_comp_not_here h_comp_store)
      ultimately show ?thesis 
        using simple_set_add by auto
    qed
    ultimately have "f ({h_comp |\<phi>| V} \<oplus>\<oplus> {?r} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I) (lnot b) \<subseteq> sem Pr {\<phi>} ?w"
      by simp
    moreover have "ver Pr ({h_comp core_i_phi_r V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I) (Assume (lnot b))"
      by (metis \<open>sem Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b)) \<subseteq> sem Pr {\<phi>} (Exhale I ; Havoc V ; Inhale I ; Assume (lnot b)) \<and> ver Pr {core_i_phi_r} (Havoc V ; Inhale I ; Assume (lnot b))\<close> sem_havoc sem_inhale sem_seq_single ver_inhale ver_seq_single)
    ultimately show ?thesis using F_def
      by (smt \<open>{h_comp core_i_phi_r V} = {h_comp |\<phi>| V} \<oplus>\<oplus> {h_comp r V}\<close> set_add_asso simple_set_add_comm)
  qed

  ultimately have "sem Pr {i_phi} ?w \<oplus>\<oplus> {?r} >> sem Pr {\<phi>} ?w"
  proof -
    have "sem Pr {i_phi} ?w \<oplus>\<oplus> {?r} >> f F (lnot b) \<oplus>\<oplus> {?r}"
      using \<open>ver Pr {i_phi} (While b I s) \<and> sem Pr {i_phi} (While b I s) >> f F (lnot b)\<close> plus_and_bigger_set by blast
    moreover have "f (F \<oplus>\<oplus> {?r}) (lnot b) >> sem Pr {\<phi>} ?w"
      using \<open>f (F \<oplus>\<oplus> {h_comp r V}) (lnot b) \<subseteq> sem Pr {\<phi>} (While b I s) \<and> ver Pr (F \<oplus>\<oplus> {h_comp r V}) (Assume (lnot b))\<close> subset_smaller by blast
    moreover have "f F (lnot b) \<oplus>\<oplus> {?r} \<subseteq> f (F \<oplus>\<oplus> {?r}) (lnot b)"
    proof (rule subsetI)
      fix x assume "x \<in> f F (lnot b) \<oplus>\<oplus> {?r}"
      then obtain ff where "ff \<in> f F (lnot b)" "Some x = Some ff \<oplus> Some ?r" 
        using elem_add_set by auto
      then have "ff \<in> F \<and> lnot b ff = Some True" using f_def by simp
      then have "b ff = Some False"
        by (meson lnot_false_true(2))
      moreover have "ff << x"
        using \<open>Some x = Some ff \<oplus> Some (h_comp r V)\<close> smaller_def by blast
      moreover have "mono Pr {x} (Assume b)" using asm_implied wfm_def mono_smono by simp
      ultimately have "b x = Some False" 
        using assume_mono_same_b smaller_refl by fastforce
      then have "lnot b x = Some True" 
        by (simp add: lnot_false_true(2))
      moreover have "x \<in> F \<oplus>\<oplus> {?r}" using \<open>ff \<in> F \<and> lnot b ff = Some True\<close> \<open>Some x = Some ff \<oplus> Some ?r\<close>
        using set_add_elem_reci by blast
      ultimately show "x \<in> f (F \<oplus>\<oplus> {h_comp r V}) (lnot b)" using f_def[of "F \<oplus>\<oplus> {?r}" "lnot b"] by simp
    qed
    ultimately show ?thesis
      by (meson bigger_set_trans subset_smaller)
  qed

  moreover have "{\<phi>} >> (F \<oplus>\<oplus> {?r})"
  proof -
    have "Some \<phi> = Some i \<oplus> s_core |\<phi>| \<oplus> Some ?r"
      by (simp add: core_inv decompo s_core_def)
    then have "{\<phi>} = {i} \<oplus>\<oplus> { |\<phi>| } \<oplus>\<oplus> {?r}"
      by (metis \<open>\<And>thesis. (\<And>i_phi. Some i_phi = Some i \<oplus> s_core \<phi> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> decompo commutative_monoid.s_core_def commutative_monoid_axioms simple_set_add)
    moreover have "{\<phi>} >> h V"
      by (simp add: V_def filter_sigma_in h_bigger)
    ultimately have "{\<phi>} >> {i} \<oplus>\<oplus> { |\<phi>| } \<oplus>\<oplus> {?r} \<oplus>\<oplus> h V"
      by (simp add: h_set_pure subset_smaller)
    moreover have "{i} >> Inh I"
      by (simp add: \<open>i \<in> Inh I\<close> subset_smaller)
    ultimately have "{\<phi>} >> Inh I \<oplus>\<oplus> { |\<phi>| } \<oplus>\<oplus> {?r} \<oplus>\<oplus> h V"
      by (meson bigger_set_trans plus_and_bigger_set)
    moreover have "{ |\<phi>| } >> { h_comp |\<phi>| V }" 
      using h_comp_smaller strongerI by fastforce
    ultimately have "{\<phi>} >> Inh I \<oplus>\<oplus> { h_comp |\<phi>| V } \<oplus>\<oplus> {?r} \<oplus>\<oplus> h V"
      by (meson \<open>{\<phi>} >> {i} \<oplus>\<oplus> {|\<phi>|} \<oplus>\<oplus> {h_comp r V} \<oplus>\<oplus> h V\<close> \<open>{i} >> Inh I\<close> bigger_set_trans bigger_sets_sum plus_and_bigger_set)
    then show ?thesis using F_def
      using set_add_asso simple_set_add_comm by auto
  qed

  moreover have "well_defined_assert b \<phi>"
  proof -
    have "ssafeMono Pr A (Assume (lnot b))" using asm_implied wfm_def
      using smono_def by blast
    then have "ver Pr {\<phi>} (Assume (lnot b))" using \<open>f (F \<oplus>\<oplus> {?r}) (lnot b) \<subseteq> sem Pr {\<phi>} ?w \<and> ver Pr (F \<oplus>\<oplus> {?r}) (Assume (lnot b))\<close> 
      by (metis \<open>\<phi> << \<phi>''\<close> \<phi>''_def(1) calculation(2) singletonD ssafeMono_def)
    then show ?thesis
      by (meson lnot_def ver_assume well_defined_assert_def)
  qed

  moreover have "i_phi << \<phi>"
    by (smt \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> associative core_add commutative_monoid.pure_smaller_ok commutative_monoid_axioms s_core_def sep_algebra.core_properties(1) sep_algebra.core_properties(2) sep_algebra_axioms smaller_def)
  then have "i_phi << \<phi>'" using asm smaller_trans by blast
  then have "i_phi << \<phi>''" using \<phi>''_def(2) smaller_trans by blast

  then show "ver Pr {\<phi>'} (inline Pr (Suc n) l (While b I s)) \<and> sem Pr {\<phi>'} (inline Pr (Suc n) l (While b I s)) >> sem Pr {\<phi>} (While b I s)"
  proof (cases "b \<phi> = Some True")
    case True

    then have "b \<phi>' = Some True"
    proof -
      have "ver Pr {\<phi>} (Assume (lnot b)) \<and> sem Pr {\<phi>} (Assume (lnot b)) = {}"
        by (meson True \<open>well_defined_assert b \<phi>\<close> can_read_not lnot_false_true(1) sem_assume_false ver_assume well_defined_assert_def)
      moreover have "smono Pr A (Assume (lnot b))" using asm_implied wfm_def[of Pr b]
        by blast
      ultimately have "ver Pr {\<phi>'} (Assume (lnot b))" using ssafeMono_def[of Pr A "Assume (lnot b)"] \<phi>''_def asm
        by (meson smono_def ssafeMono_singleton)
      then have "sem Pr {\<phi>'} (Assume (lnot b)) >> {}" using smonoOut_def[of Pr A "Assume (lnot b)"] \<phi>''_def asm
        by (metis \<open>smono Pr A (Assume (lnot b))\<close> \<open>ver Pr {\<phi>} (Assume (lnot b)) \<and> sem Pr {\<phi>} (Assume (lnot b)) = {}\<close> smonoOut_singleton smono_def)
      then have "f {\<phi>'} (lnot b) = {}"
        using \<open>ver Pr {\<phi>'} (Assume (lnot b))\<close> bigger_set_def sem_assume_filter by fastforce
      then have "lnot b \<phi>' \<noteq> Some True"
        using general_same_f by blast
      moreover have "lnot b \<phi>' \<noteq> None" using \<open>ver Pr {\<phi>'} (Assume (lnot b))\<close> ver_assume[of Pr \<phi>'] by simp
      ultimately show ?thesis
        using lnot_false_true(1) by fastforce
    qed

    moreover have "\<phi>'' \<in> f A b"
    proof -
      have "lnot b \<phi>' = Some False"
        by (meson calculation lnot_false_true(1))
      moreover have "mono Pr A (Assume (lnot b))" using asm
        using asm_implied mono_smono wfm_def by blast
      then have "lnot b \<phi>' = lnot b \<phi>''" using
       assume_mono_same_b[of Pr A "lnot b" \<phi>' \<phi>'']
        using \<phi>''_def(1) \<phi>''_def(2) calculation smaller_refl by fastforce
      then have "b \<phi>'' = Some True"
        using calculation lnot_false_true(1) by fastforce
      then show ?thesis using f_def
        by (simp add: \<phi>''_def(1))
    qed


    moreover have R1: "ver Pr (f F b) s \<and> sem Pr (f F b) s >> F \<and> ver Pr F (Assume b)"
    proof -
      have "ver Pr F (Assume b)" 
        using \<open>ver Pr F (Assume b) \<and> sem Pr F (Assume b) = f F b\<close> by linarith
      moreover have "ver Pr (f F b) s \<and> sem Pr (f F b) s >> Inh I"
        using \<open>ver Pr (f F b) s \<and> sem Pr (f F b) s >> Inh I\<close> by blast
      moreover have "sem Pr (f F b) s >> {h_comp |\<phi>| V} \<oplus>\<oplus> h V"
      proof -
        have "sem Pr (f F b) s >> {h_comp |\<phi>| V}"
        proof (rule greaterI)
          fix y assume "y \<in> sem Pr (f F b) s"
          then obtain x where "x \<in> f F b" "y \<in> sem Pr {x} s" 
            using elem_sem by blast
          then have "ver Pr {x} s" 
            using calculation(2) v_singleton by blast
          then have "sem Pr {x} s >> {h_comp |x| (modif s)}" using asm 
            using \<open>wf_stmt Pr s\<close> statement_doesnt_modif by blast
          moreover have "{h_comp |x| (modif s)} >> {h_comp |\<phi>| V}"
          proof -
            have "{x} >> F" 
              by (meson \<open>x \<in> f F b\<close> f_inclusion sep_algebra.bigger_set_forall sep_algebra_axioms subset_smaller)
            moreover have "F >> {h_comp |\<phi>| V}" 
              by (simp add: F_def rel_bigger_add_set set_add_asso)
            ultimately have "{x} >> {h_comp |\<phi>| V}" 
              using bigger_set_trans by blast
            then have "{ |x| } >> { |h_comp |\<phi>| V| }"
              by (metis bigger_set_def singletonD singletonI smaller_core_comp)
            then have "{h_comp |x| (modif s)} >> {h_comp |h_comp |\<phi>| V| (modif s)}" 
              by (metis bigger_set_def core_properties(1) h_comp_sum_set_smaller_pure pure_set_add_smaller simple_set_add_comm singletonD singletonI)
            moreover have "h_comp |h_comp |\<phi>| V| (modif s) = h_comp |\<phi>| V" 
              by (smt Diff_cancel Int_Diff V_def core_properties(1) filter_sigma_in h_comp_not_here h_comp_smaller h_comp_store not_pure_core smaller_pure store_pure)
            ultimately show ?thesis by simp
          qed
          ultimately show "\<exists>x\<in>{h_comp |\<phi>| V}. x << y" 
            by (meson \<open>y \<in> sem Pr {x} s\<close> bigger_set_def smaller_trans)
        qed
        moreover have "sem Pr (f F b) s >> h V"
        proof (rule greaterI)
          fix y assume "y \<in> sem Pr (f F b) s"
          then have "y \<in> sem Pr F (Assume b ; s)" 
            using \<open>ver Pr (f F b) s \<and> sem Pr (f F b) s >> Inh I\<close> \<open>ver Pr F (Assume b) \<and> sem Pr F (Assume b) = f F b\<close> sem_seq ver_seq by presburger
          then obtain x where "x \<in> F" "y \<in> sem Pr {x} (Assume b ; s)" 
            using elem_sem by blast
          then have "set V \<subseteq> \<sigma> x"
          proof -
            have "{x} >> h V"
              by (metis F_def \<open>x \<in> F\<close> bigger_set_forall bigger_set_trans rel_bigger_add_set simple_set_add_comm)
            then show ?thesis
              by (metis Un_commute bigger_set_def h_pure h_store pure_smaller_ok singletonI store_add subset_Un_eq)
          qed
          moreover have "ver Pr {x} (Assume b ; s)"
            by (metis \<open>ver Pr (f F b) s \<and> sem Pr (f F b) s >> Inh I\<close> \<open>ver Pr F (Assume b) \<and> sem Pr F (Assume b) = f F b\<close> \<open>x \<in> F\<close> v_singleton ver_seq)
          ultimately have "\<sigma> x \<subseteq> \<sigma> y" using store_modif_sem[of Pr] asm asm_implied 
            by (meson \<open>\<And>thesis. (\<lbrakk>wf_stmt Pr s; set (modif s) \<subseteq> set l; wf_assert I\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>y \<in> sem Pr {x} (Assume b ; s)\<close> wf_stmt.simps(1) wf_stmt.simps(8))
          then have "{y} >> h V" 
            using \<open>set V \<subseteq> \<sigma> x\<close> h_bigger by auto
          then show "\<exists>x\<in>h V. x << y" 
            using bigger_set_def by blast
        qed
        ultimately show ?thesis
          using h_set_pure by blast
      qed
      ultimately have "sem Pr (f F b) s >> Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V" 
        by (smt add_pure_singleton bigger_set_trans core_properties(1) h_comp_smaller h_set_pure rel_bigger_add_set simple_set_add_comm smaller_pure)
      then show ?thesis 
        using F_def \<open>ver Pr (f F b) s \<and> sem Pr (f F b) s >> Inh I\<close> \<open>ver Pr F (Assume b)\<close> set_add_asso simple_set_add_comm by auto
    qed

    then have R2: "ver Pr {\<phi>'} ?s' \<and> sem Pr {\<phi>'} ?s' >> F \<oplus>\<oplus> {?r}"
    proof -
      have "{i_phi} >> Inh I \<oplus>\<oplus> {|\<phi>|}"
        by (metis (mono_tags, lifting) \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>i \<in> Inh I\<close> commutative_monoid.s_core_def commutative_monoid_axioms set_add_elem_reci singletonD singletonI subsetI subset_smaller)
      moreover have "{ |\<phi>| } >> {h_comp |\<phi>| V} \<oplus>\<oplus> h V"
      proof -
        have "{ |\<phi>| } >> {h_comp |\<phi>| V}"
          using h_comp_smaller strongerI by fastforce
        moreover have "{ |\<phi>| } >> h V"
        proof -
          have "set V \<subseteq> \<sigma> \<phi>" using filter_sigma_in V_def by simp
          then show ?thesis
            using h_bigger store_pure by auto
        qed
        ultimately show ?thesis
          using h_set_pure by blast
      qed
      ultimately have "{i_phi} >> Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V"
        by (smt add_sets_neutral bigger_set_forall bigger_set_trans bigger_sets_sum plus_and_bigger_set rel_bigger_add_set set_add_asso simple_set_add_comm)
      then have "{i_phi} >> f (Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V) b"
      proof -
        obtain xx where "xx \<in> Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V" "xx << i_phi"
          using \<open>{i_phi} >> Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> bigger_set_def by auto
        then have "ver Pr {xx} (Assume b)"
          using F_def R1 set_add_asso simple_set_add_comm v_singleton by blast
        then have "b xx \<noteq> None"
          by (simp add: ver_assume)
        then have "b xx = Some True"
        proof -
          have "xx << \<phi>" 
            using \<open>i_phi << \<phi>\<close> \<open>xx << i_phi\<close> smaller_trans by blast
          moreover have "mono Pr A (Assume b)" using asm_implied 
            using mono_smono wfm_def by blast
          ultimately show ?thesis using assume_mono_same_b[of Pr A b xx \<phi>]
            using True \<open>\<phi> << \<phi>''\<close> \<open>b xx \<noteq> None\<close> \<phi>''_def(1) by auto
        qed
        then have "xx \<in> f (Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V) b" using f_def \<open>xx \<in> Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> by simp
        then show ?thesis
          by (metis \<open>xx << i_phi\<close> singletonD strongerI)
      qed

      then obtain xx where "xx \<in> f (Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V) b" "xx << i_phi"
        using bigger_set_def by auto
      then have "ver Pr {xx} s"
        by (metis F_def R1 set_add_asso simple_set_add_comm v_singleton)
      then have "ver Pr {i_phi} (inline Pr n l s) \<and> sem Pr {i_phi} (inline Pr n l s) >> sem Pr {xx} s"
      proof -
        have "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr s"
          using asm by simp
        moreover have "no_inter A l \<and> set (modif s) \<subseteq> set l  \<and> xx << i_phi \<and> ver Pr {xx} s"
          using asm \<open>set (modif s) \<subseteq> set l\<close> \<open>ver Pr {xx} s\<close> \<open>xx << i_phi\<close> by blast
        moreover have "SC Pr n (f A b) l s"
          using asm by auto
        ultimately show ?thesis using instantiate_SP[of Pr n "f A b" l s i_phi xx] asm assms
          by (metis (no_types, lifting) UnCI \<open>\<phi>'' \<in> f A b\<close> \<open>i_phi << \<phi>''\<close> f_inclusion no_inter_def subset_Un_eq)
      qed
      moreover have "framing Pr (f A b) (inline Pr n l s)"
        using asm_implied by blast
      ultimately have "ver Pr {\<phi>'} ?s'"
        using \<open>\<phi>'' \<in> f A b\<close> \<phi>''_def(2) framing.simps smono_def ssafeMono_singleton \<open>i_phi << \<phi>'\<close> by blast
      moreover have "ver Pr {\<phi>} ?s'"
        using \<open>\<phi> << \<phi>''\<close> \<open>\<phi>'' \<in> f A b\<close> \<open>i_phi << \<phi>\<close> \<open>ver Pr {i_phi} (inline Pr n l s) \<and> sem Pr {i_phi} (inline Pr n l s) >> sem Pr {xx} s\<close> asm_implied framing.simps smono_def ssafeMono_singleton by blast
      ultimately have "sem Pr {\<phi>'} ?s' >> sem Pr {\<phi>} ?s'"
      proof -
        have "\<phi> << \<phi>'" using asm by simp
        moreover have "smonoOut Pr (f A b) ?s'"
          using asm_implied framing.simps smono_def by blast
        ultimately show ?thesis 
          using \<open>\<phi>'' \<in> f A b\<close> \<open>ver Pr {\<phi>} (inline Pr n l s)\<close> \<phi>''_def(2) smonoOut_singleton by blast
      qed
      moreover have "{\<phi>} = {i_phi} \<oplus>\<oplus> {?r}"
        using \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> decompo simple_set_add by presburger
      moreover have "set (modif (inline Pr n l s)) \<inter> \<sigma> ?r = {}"
      proof -
        have "set (modif (inline Pr n l s)) \<inter> \<sigma> ?r \<subseteq> {}"
        proof (rule subsetI)
          fix x assume "x \<in> set (modif (inline Pr n l s)) \<inter> \<sigma> (h_comp r V)"
          then have "x \<in> \<sigma> r - set V"
            by (simp add: h_comp_store)
          then have "x \<in> \<sigma> r - (\<sigma> \<phi> \<inter> set (modif s))"
            by (simp add: Int_commute V_def filter_sigma_in)
          moreover have "\<sigma> r \<subseteq> \<sigma> \<phi>"
          proof -
            have "r << \<phi>"
              by (metis \<open>Some \<phi> = Some i \<oplus> Some r\<close> commutative commutative_monoid.smaller_def commutative_monoid_axioms)
            then show ?thesis
              using \<open>Some \<phi> = Some i \<oplus> Some r\<close> store_add by blast
          qed
          moreover have "x \<in> set (modif s)"
          proof -
            have "set l \<inter> set (modif ?s') \<subseteq> set (modif s)" using asm no_inter_inline_general by simp
            moreover have "\<sigma> \<phi>'' \<subseteq> set l" using asm no_inter_def no_inter_single_def
              by (simp add: \<phi>''_def(1))
            moreover have "r << \<phi>''"
              by (metis (full_types) \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>\<phi> << \<phi>''\<close> commutative smaller_def smaller_trans)
            then have "\<sigma> r \<subseteq> \<sigma> \<phi>''"
              using smaller_def store_add by auto
            then have "x \<in> set l"
              using \<open>x \<in> \<sigma> r - set V\<close> calculation(2) by auto
            ultimately show ?thesis
              using \<open>x \<in> set (modif (inline Pr n l s)) \<inter> \<sigma> (h_comp r V)\<close> by blast
          qed
          ultimately show "x \<in> {}"
            by blast
        qed
        then show ?thesis by blast
      qed
      ultimately have "sem Pr {\<phi>} ?s' >> sem Pr {i_phi} ?s' \<oplus>\<oplus> {?r}"
        using framing.simps[of Pr "f A b" ?s']
        by (smt \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>\<phi> << \<phi>''\<close> \<open>\<phi>'' \<in> f A b\<close> \<open>framing Pr (f A b) (inline Pr n l s)\<close> \<open>ver Pr {i_phi} (inline Pr n l s) \<and> sem Pr {i_phi} (inline Pr n l s) >> sem Pr {xx} s\<close> decompo)
      then have "sem Pr {\<phi>} ?s' >> sem Pr {xx} s \<oplus>\<oplus> {?r}" 
        by (meson \<open>ver Pr {i_phi} (inline Pr n l s) \<and> sem Pr {i_phi} (inline Pr n l s) >> sem Pr {xx} s\<close> bigger_set_trans plus_and_bigger_set)
      moreover have "sem Pr {xx} s >> {h_comp |\<phi>| V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I"
      proof -
        have "sem Pr {xx} s >> sem Pr (f (Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V) b) s"
          by (meson \<open>xx \<in> f (Inh I \<oplus>\<oplus> {h_comp |\<phi>| V} \<oplus>\<oplus> h V) b\<close> elem_sem smaller_refl strongerI)
        then show ?thesis
          by (smt F_def R1 bigger_set_trans set_add_asso simple_set_add_comm)
      qed
      ultimately show ?thesis
        using F_def \<open>sem Pr {\<phi>'} (inline Pr n l s) >> sem Pr {\<phi>} (inline Pr n l s)\<close> \<open>ver Pr {\<phi>'} (inline Pr n l s)\<close> bigger_set_trans plus_and_bigger_set set_add_asso simple_set_add_comm
        by meson
    qed

    have R3: "ver Pr F ?w \<and> sem Pr F ?w >> sem Pr {i_phi} ?w"
    proof (rule verBiggerI)
      fix x assume "x \<in> F"
      define V' where "V' = filter_sigma x (modif s)"


          have "x \<in> {h_comp |\<phi>| V} \<oplus>\<oplus> h V \<oplus>\<oplus> Inh I"
            using F_def \<open>x \<in> F\<close> by blast
          then obtain hh ii where "ii \<in> Inh I" "hh \<in> {h_comp |\<phi>| V} \<oplus>\<oplus> h V" "Some x = Some hh \<oplus> Some ii" 
            using elem_add_set by auto
          then obtain hv where "hv \<in> h V" "Some hh = Some (h_comp |\<phi>| V) \<oplus> Some hv" 
            using elem_add_set by auto
          moreover have "\<sigma> ii \<subseteq> \<sigma> \<phi>"
          proof -
            have "x \<in> sem Pr { |\<phi>| } (Havoc V ; Inhale I)" 
              using \<open>ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) \<and> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) = F\<close> \<open>ver Pr {|\<phi>|} (Havoc V) \<and> sem Pr {|\<phi>|} (Havoc V) = {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> \<open>x \<in> F\<close> sem_seq ver_seq_single by presburger
            thm store_modif_sem
            moreover have "ver Pr { |\<phi>| } (Havoc V ; Inhale I)"
              using \<open>ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) \<and> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) = F\<close> \<open>ver Pr {|\<phi>|} (Havoc V) \<and> sem Pr {|\<phi>|} (Havoc V) = {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> ver_seq_single by auto
            moreover have "wf_stmt Pr (Havoc V ; Inhale I)" 
              by (simp add: \<open>wf_assert I\<close>)
            ultimately have "\<sigma> x \<subseteq> \<sigma> |\<phi>| \<union> set (modif (Havoc V ; Inhale I))" using store_modif_sem asm by blast
            moreover have "modif (Havoc V ; Inhale I) = V" by simp
            ultimately have "\<sigma> x \<subseteq> \<sigma> \<phi>" 
              using V_def filter_sigma_in store_pure by auto
            moreover have "\<sigma> ii \<subseteq> \<sigma> x" using \<open>Some x = Some hh \<oplus> Some ii\<close>
              by (simp add: store_add)
            ultimately show ?thesis 
              by blast
          qed
          then obtain y where "y \<in> sem Pr { |\<phi>| } (Havoc V)" "x \<in> sem Pr {y} (Inhale I)"
            using \<open>ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) \<and> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I) = F\<close> \<open>ver Pr {|\<phi>|} (Havoc V) \<and> sem Pr {|\<phi>|} (Havoc V) = {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> \<open>x \<in> F\<close> by auto
          moreover have "\<sigma> hh = \<sigma> \<phi>"
          proof -
            have "\<sigma> hh = \<sigma> (h_comp |\<phi>| V) \<union> set V"
              using calculation(1) calculation(2) h_store store_add by blast
            then have "\<sigma> hh = (\<sigma> \<phi> - set V) \<union> set V" 
              using h_comp_store store_pure by auto
            moreover have "set V \<subseteq> \<sigma> \<phi>" using V_def 
              by (simp add: filter_sigma_in)
            ultimately show ?thesis 
              by blast
          qed
          ultimately have "|ii| << |hh|"
          proof -
            have "\<sigma> |ii| \<subseteq> \<sigma> |hh|" 
              using \<open>\<sigma> hh = \<sigma> \<phi>\<close> \<open>\<sigma> ii \<subseteq> \<sigma> \<phi>\<close> store_pure by auto
            moreover have "|ii| ## |hh|" 
              by (metis (full_types) Option.is_none_def \<open>Some x = Some hh \<oplus> Some ii\<close> definedness(2) definedness(3) h_comp_some_exists not_None_eq option.inject orig_comm orig_neutral plus.simps(1) commutative_monoid.defined_def commutative_monoid.plus.elims commutative_monoid_axioms s_core_def sep_algebra.defined_trans_plus sep_algebra.definedness(2) sep_algebra.definedness(3) sep_algebra_axioms)
            ultimately show ?thesis 
              by (simp add: \<open>|ii| ## |hh|\<close> compatible_stores core_properties(1))
          qed
          then have "|x| = |hh|" 
            by (metis \<open>Some x = Some hh \<oplus> Some ii\<close> core_add core_properties(1) option.inject pure_smaller_ok s_core_def)
          then have "s_core x = Some (h_comp |\<phi>| V) \<oplus> s_core hv" 
            by (metis \<open>Some hh = Some (h_comp |\<phi>| V) \<oplus> Some hv\<close> core_add core_inv h_comp_only_pure neutral properties_c(1) pure_u s_core_def unique_c)
          moreover have "V = V'" using filter_sigma_same V_def V'_def 
            using \<open>Some x = Some hh \<oplus> Some ii\<close> \<open>\<sigma> hh = \<sigma> \<phi>\<close> \<open>\<sigma> ii \<subseteq> \<sigma> \<phi>\<close> store_add by blast
          ultimately have "h_comp |x| V' = h_comp |\<phi>| V" 
          proof -
            have "Some (h_comp |x| V') = Some (h_comp (h_comp |\<phi>| V) V') \<oplus> Some (h_comp |hv| V')"
              using \<open>s_core x = Some (h_comp |\<phi>| V) \<oplus> s_core hv\<close> h_comp_lin s_core_def by auto
            moreover have "h_comp (h_comp |\<phi>| V) V' = h_comp |\<phi>| V" 
              by (simp add: \<open>V = V'\<close> h_comp_not_here h_comp_store)
            moreover have "|hv| = hv" 
              using \<open>hv \<in> h V\<close> h_pure not_pure_core by auto
            then have "h_comp hv V = u"
              by (simp add: \<open>hv \<in> h V\<close> h_comp_h)
            ultimately show ?thesis
              using \<open>V = V'\<close> \<open>|hv| = hv\<close> neutral 
              by force
          qed
          then have "{h_comp |x| V'} \<oplus>\<oplus> h V' = {h_comp |\<phi>| V} \<oplus>\<oplus> h V" 
            by (simp add: \<open>V = V'\<close> \<open>h_comp |x| V' = h_comp |\<phi>| V\<close>)


      then have "ver Pr {x} (Exhale I ; Havoc V' ; Inhale I ; Assume (lnot b)) \<and> sem Pr {x} (Exhale I ; Havoc V' ; Inhale I ; Assume (lnot b)) >> sem Pr {i_phi} ?w"
      proof -
        have "ver Pr {x} (Exhale I)" 
          by (metis F_def \<open>wf_assert I\<close> \<open>x \<in> F\<close> bigger_set_forall rel_bigger_add_set simple_set_add_comm supported_intui_exhale)
        moreover have "sem Pr {x} (Exhale I) >> { |x| }" using exhale_sem_bigger_core_bigger
          by (metis F_def \<open>wf_assert I\<close> \<open>x \<in> F\<close> bigger_set_def rel_bigger_add_set simple_set_add_comm)
        moreover have "mono Pr (sem Pr {x} (Exhale I)) (Havoc V')" 
          using havoc_smono mono_smono by blast
        moreover have "ver Pr { |x| } (Havoc V')" 
          using V'_def filter_sigma_in store_pure ver_havoc by auto
        ultimately have "ver Pr (sem Pr {x} (Exhale I)) (Havoc V') \<and> sem Pr (sem Pr {x} (Exhale I)) (Havoc V') >> sem Pr { |x| } (Havoc V')"
          using havoc_smono smaller_refl smono_def ssafeMono_def smonoOut_def 
          by (meson mono_smono)
        then have "sem Pr {x} (Exhale I ; Havoc V') >> {h_comp |x| V'} \<oplus>\<oplus> h V'" 
          by (metis \<open>ver Pr {x} (Exhale I)\<close> \<open>ver Pr {|x|} (Havoc V')\<close> sem_havoc sem_seq ver_seq_single)

        moreover have incl: "{h_comp |\<phi>| V} \<oplus>\<oplus> h V \<subseteq> sem Pr {i_phi} (Exhale I ; Havoc V')"
        proof -
          have "{ |i_phi| } \<subseteq> sem Pr {i_phi} (Exhale I)" 
            using \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> \<open>i \<in> Inh I\<close> \<open>wf_assert I\<close> core_add core_properties(1) core_properties(3) s_core_def simple_sem_exhale by auto
          moreover have "|i_phi| = |\<phi>|"
          proof -
            have "|i| << |\<phi>|" 
              using \<open>Some \<phi> = Some i \<oplus> Some r\<close> smaller_core_comp smaller_def by blast
            then show ?thesis 
              by (smt \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> commutative core_inv core_properties(1) option.sel pure_smaller_ok s_core_def sep_algebra.core_add sep_algebra_axioms)
          qed
          moreover have "{h_comp |\<phi>| V} \<oplus>\<oplus> h V = sem Pr { |\<phi>| } (Havoc V')"
            using \<open>V = V'\<close> \<open>ver Pr {|\<phi>|} (Havoc V) \<and> sem Pr {|\<phi>|} (Havoc V) = {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> by blast
          moreover have "sem Pr { |i_phi| } (Havoc V') \<subseteq> sem Pr (sem Pr {i_phi} (Exhale I)) (Havoc V')" 
            using \<open>V = V'\<close> calculation(1) elem_sem by blast
          moreover have "{h_comp |\<phi>| V} \<oplus>\<oplus> h V = sem Pr { |i_phi| } (Havoc V')" 
            using calculation(2) calculation(3) by auto
          moreover have "ver Pr (sem Pr {i_phi} (Exhale I)) (Havoc V')" 
          proof -
            obtain aa :: "('a, 'b, 'c) stmt \<Rightarrow> 'a set \<Rightarrow> (char list \<times> 'b list \<times> 'b list \<times> ('a \<Rightarrow> bool option) \<times> ('a \<Rightarrow> bool option) \<times> ('a, 'b, 'c) stmt) list \<Rightarrow> 'a" where
              f1: "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x1 \<and> \<not> ver x2 {v3} x0) = (aa x0 x1 x2 \<in> x1 \<and> \<not> ver x2 {aa x0 x1 x2} x0)"
              by moura
            have "aa (Havoc V') (sem Pr {i_phi} (Exhale I)) Pr \<notin> sem Pr {i_phi} (Exhale I) \<or> ver Pr {aa (Havoc V') (sem Pr {i_phi} (Exhale I)) Pr} (Havoc V')"
              by (metis \<open>\<sigma> hh = \<sigma> \<phi>\<close> \<open>ver Pr {i_phi} (While b I s) \<and> sem Pr {i_phi} (While b I s) >> f F (lnot b)\<close> \<open>ver Pr {|x|} (Havoc V')\<close> \<open>|x| = |hh|\<close> calculation(2) store_pure store_same_pred_supp_exhale ver_havoc ver_loop ver_seq_single)
            then show ?thesis
              using f1 by (meson v_singleton)
          qed
          moreover have "sem Pr (sem Pr {i_phi} (Exhale I)) (Havoc V') = sem Pr {i_phi} (Exhale I ; Havoc V')" 
            by (metis \<open>ver Pr {i_phi} (While b I s) \<and> sem Pr {i_phi} (While b I s) >> f F (lnot b)\<close> calculation(6) sem_seq ver_loop ver_seq_single)
          ultimately show ?thesis by simp
        qed

        then have "{h_comp |\<phi>| V} \<oplus>\<oplus> h V >> sem Pr {i_phi} (Exhale I ; Havoc V')" 
          using subset_smaller by blast
        then have "ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I ; Assume (lnot b)) \<and> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I ; Assume (lnot b)) >> sem Pr {i_phi} ?w"
        proof -
          have "ver Pr {i_phi} ?w" 
            using \<open>ver Pr {i_phi} (While b I s) \<and> sem Pr {i_phi} (While b I s) >> f F (lnot b)\<close> by blast
          moreover have "filter_sigma i_phi (modif s) = V'"
          proof -
            have "\<sigma> i_phi = \<sigma> x"
            proof -
              have "\<sigma> x = \<sigma> \<phi>" 
                by (metis \<open>\<sigma> hh = \<sigma> \<phi>\<close> \<open>|x| = |hh|\<close> store_pure)
              moreover have "\<sigma> i \<subseteq> \<sigma> \<phi>"
              proof -
                have "i << \<phi>" 
                  using \<open>Some \<phi> = Some i \<oplus> Some r\<close> smaller_def by blast
                then show ?thesis 
                  by (simp add: \<open>Some \<phi> = Some i \<oplus> Some r\<close> store_add)
              qed
              moreover have "\<sigma> i_phi = \<sigma> i \<union> \<sigma> |\<phi>|" 
                by (simp add: \<open>Some i_phi = Some i \<oplus> s_core \<phi>\<close> s_core_def store_add)
              ultimately show ?thesis 
                using store_pure by auto
            qed
            then show ?thesis
              using V'_def filter_sigma_same by blast
          qed
          then have "ver Pr {i_phi} (Exhale I ; Havoc V' ; Inhale I ; Assume (lnot b))" using ver_loop 
            using calculation by blast
          then have "ver Pr (sem Pr {i_phi} (Exhale I ; Havoc V')) (Inhale I ; Assume (lnot b))" 
            using ver_asso ver_seq by blast
          then have "ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I ; Assume (lnot b))" using incl 
            by (meson subset_iff v_singleton)
          moreover have "sem Pr {i_phi} ?w = sem Pr (sem Pr {i_phi} (Exhale I ; Havoc V')) (Inhale I ; Assume (lnot b))" 
            by (metis \<open>filter_sigma i_phi (modif s) = V'\<close> \<open>ver Pr (sem Pr {i_phi} (Exhale I ; Havoc V')) (Inhale I ; Assume (lnot b))\<close> \<open>ver Pr {i_phi} (Exhale I ; Havoc V' ; Inhale I ; Assume (lnot b))\<close> calculation(1) sem_loop sem_seq ver_seq_single)
          then have "sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I ; Assume (lnot b)) \<subseteq> sem Pr (sem Pr {i_phi} (Exhale I ; Havoc V')) (Inhale I ; Assume (lnot b))"
            using incl by (meson elem_sem subset_eq)
          then show ?thesis using incl 
            using \<open>sem Pr {i_phi} (While b I s) = sem Pr (sem Pr {i_phi} (Exhale I ; Havoc V')) (Inhale I ; Assume (lnot b))\<close> calculation(2) subset_smaller by presburger
        qed

        ultimately have "ver Pr { |x| } (Havoc V' ; Inhale I ; Assume (lnot b))" 
          by (metis (no_types, lifting) \<open>V = V'\<close> \<open>h_comp |x| V' = h_comp |\<phi>| V\<close> \<open>ver Pr {|x|} (Havoc V')\<close> sem_havoc sem_seq_single ver_seq)
        moreover have "sem Pr { |x| } (Havoc V' ; Inhale I ; Assume (lnot b)) >> sem Pr {i_phi} ?w"
          by (smt \<open>V = V'\<close> \<open>h_comp |x| V' = h_comp |\<phi>| V\<close> \<open>ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I ; Assume (lnot b)) \<and> sem Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I ; Assume (lnot b)) >> sem Pr {i_phi} (While b I s)\<close> \<open>ver Pr {|x|} (Havoc V')\<close> sem_havoc sem_seq ver_seq)

        moreover have "mono Pr (sem Pr {x} (Exhale I)) (Havoc V' ; Inhale I ; Assume (lnot b))"
        proof (rule mono_comp)
          let ?A = "sem Pr {x} (Exhale I)"
          have "mono Pr ?A (Havoc V' ; Inhale I)"
          proof (rule mono_comp)
            show "smono Pr ?A (Havoc V')" 
              using havoc_smono by blast
            show "smono Pr (sem_ver Pr (fill_set ?A) (Havoc V')) (Inhale I)"
              using \<open>wf_assert I\<close> inhale_smono by blast
            show "\<And>xa y. \<exists>a\<in>sem Pr {x} (Exhale I). xa << a \<and> y \<in> sem Pr {xa} (Havoc V') \<and> ver Pr {xa} (Havoc V') \<Longrightarrow> \<exists>z\<in>(sem_ver Pr (fill_set ?A) (Havoc V')). y << z"
            proof -
              fix xa y assume "\<exists>a\<in>sem Pr {x} (Exhale I). xa << a \<and> y \<in> sem Pr {xa} (Havoc V') \<and> ver Pr {xa} (Havoc V')"
              then obtain a where asm4: "a \<in> ?A \<and> xa << a \<and> y \<in> sem Pr {xa} (Havoc V') \<and> ver Pr {xa} (Havoc V')" by blast
              then have "y \<in> sem_ver Pr (fill_set ?A) (Havoc V')" using fill_set_sem_ver by blast
              then show "\<exists>z\<in>(sem_ver Pr (fill_set ?A) (Havoc V')). y << z" 
                using smaller_refl by blast
            qed
          qed
          then show "smono Pr (sem Pr {x} (Exhale I)) (Havoc V' ; Inhale I)" using mono_smono by simp
          let ?B = "sem_ver Pr (fill_set ?A) (Havoc V' ; Inhale I)"
          show "smono Pr ?B (Assume (lnot b))" using asm_implied wfm_def mono_smono by simp
          show "\<And>xa y. \<exists>a\<in>?A. xa << a \<and> y \<in> sem Pr {xa} (Havoc V' ; Inhale I) \<and> ver Pr {xa} (Havoc V' ; Inhale I) \<Longrightarrow> \<exists>z\<in>?B. y << z"
          proof -
            fix xa y assume "\<exists>a\<in>?A. xa << a \<and> y \<in> sem Pr {xa} (Havoc V' ; Inhale I) \<and> ver Pr {xa} (Havoc V' ; Inhale I)"
            then obtain a where asm4: "a\<in>?A \<and> xa << a \<and> y \<in> sem Pr {xa} (Havoc V' ; Inhale I) \<and> ver Pr {xa} (Havoc V' ; Inhale I)" by blast
            then have "y \<in> ?B" using fill_set_sem_ver by blast
            then show "\<exists>z\<in>?B. y << z" 
              using smaller_refl by blast
          qed
        qed
        ultimately have "ver Pr (sem Pr {x} (Exhale I)) (Havoc V' ; Inhale I ; Assume (lnot b))" using
\<open>sem Pr {x} (Exhale I) >> { |x| }\<close> ssafeMono_def[of Pr "sem Pr {x} (Exhale I)"] \<open>ver Pr { |x| } (Havoc V' ; Inhale I ; Assume (lnot b))\<close> smono_def
        smaller_refl mono_smono by blast
        then have "sem Pr (sem Pr {x} (Exhale I)) (Havoc V' ; Inhale I ; Assume (lnot b)) >> sem Pr { |x| } (Havoc V' ; Inhale I ; Assume (lnot b))"
          using
          \<open>sem Pr {x} (Exhale I) >> { |x| }\<close> smonoOut_def[of Pr "sem Pr {x} (Exhale I)"] \<open>ver Pr { |x| } (Havoc V' ; Inhale I ; Assume (lnot b))\<close> smono_def
            using \<open>mono Pr (sem Pr {x} (Exhale I)) (Havoc V' ; Inhale I ; Assume (lnot b))\<close> mono_smono smaller_refl by blast
        then show ?thesis 
          by (smt \<open>sem Pr (sem Pr {x} (Exhale I)) (Havoc V' ; Inhale I ; Assume (lnot b)) >> sem Pr {|x|} (Havoc V' ; Inhale I ; Assume (lnot b))\<close> \<open>sem Pr {|x|} (Havoc V' ; Inhale I ; Assume (lnot b)) >> sem Pr {i_phi} (While b I s)\<close> \<open>ver Pr (sem Pr {x} (Exhale I)) (Havoc V' ; Inhale I ; Assume (lnot b))\<close> \<open>ver Pr {x} (Exhale I)\<close> bigger_set_trans sem_seq ver_seq)
      qed

      moreover have "ver Pr { |x| } (Havoc V' ; Inhale I ; Assume b ; s ; Exhale I)"
      proof -
        have "ver Pr { |x| } (Havoc V')"
          using V'_def filter_sigma_in store_pure ver_havoc by auto
        then have "sem Pr { |x| } (Havoc V') = {h_comp |x| V'} \<oplus>\<oplus> h V'"
          using sem_havoc by blast
        moreover have "ver Pr ({h_comp |\<phi>| V} \<oplus>\<oplus> h V) (Inhale I ; Assume b ; s ; Exhale I)" 
          by (smt \<open>ver Pr {|\<phi>|} (Havoc V ; Inhale I ; Assume b ; s ; Exhale I)\<close> \<open>ver Pr {|\<phi>|} (Havoc V) \<and> sem Pr {|\<phi>|} (Havoc V) = {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close> sem_seq ver_seq)
        ultimately have "ver Pr ({h_comp |x| V'} \<oplus>\<oplus> h V') (Inhale I ; Assume b ; s ; Exhale I)" 
          by (simp add: \<open>{h_comp |x| V'} \<oplus>\<oplus> h V' = {h_comp |\<phi>| V} \<oplus>\<oplus> h V\<close>)
        then show ?thesis 
          by (metis \<open>sem Pr {|x|} (Havoc V') = {h_comp |x| V'} \<oplus>\<oplus> h V'\<close> \<open>ver Pr ({h_comp |x| V'} \<oplus>\<oplus> h V') (Inhale I ; Assume b ; s ; Exhale I)\<close> \<open>ver Pr {|x|} (Havoc V')\<close> ver_asso ver_seq)
      qed
      ultimately show "ver Pr {x} (While b I s) \<and> sem Pr {x} (While b I s) >> sem Pr {i_phi} (While b I s)"
        using ver_loop sem_loop V'_def by metis
    qed

    let ?F = "Set.filter (\<lambda>ff. \<exists>y \<in> sem Pr {\<phi>'} ?s'. ff << y) F"

    have R4: "ver Pr ?F ?w' \<and> sem Pr ?F ?w' >> sem Pr F ?w"
    proof (rule verBiggerI)
      fix x assume asm3: "x \<in> ?F"

      let ?A = "sem_ver Pr (fill_set (f A b)) ?s'"

      have "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr (While b I s) \<and> SC Pr n ?A (l @ read (inline Pr n l s)) (While b I s) \<and> set (modif (While b I s)) \<subseteq> set (l @ modif ?s')"
        using asm asm_implied by auto
      moreover have "no_inter ?A (l @ read ?s')"
      proof (rule no_inter_I)
        fix a assume "a \<in> sem_ver Pr (fill_set (f A b)) (inline Pr n l s)"
        then obtain aa where "aa \<in> fill_set (f A b)" "a \<in> sem Pr {aa} ?s'" "ver Pr {aa} ?s'" using sem_ver_def by auto
        then have "\<sigma> aa \<subseteq> set l"
        proof -
          obtain y where "y \<in> f A b" "aa << y"
            using \<open>aa \<in> fill_set (f A b)\<close> elem_fill_set by blast
          then have "y \<in> A"
            using f_inclusion by blast
          then have "\<sigma> y \<subseteq> set l" using asm
            by (simp add: no_inter_def no_inter_single_def)
          then show ?thesis 
            by (metis Un_assoc \<open>aa << y\<close> core_properties(1) pure_smaller_ok smaller_core_comp store_add store_pure sup.orderE sup.orderI)
        qed
        moreover have "\<sigma> a \<subseteq> \<sigma> aa \<union> set (modif ?s')" using store_modif_sem asm 
          using \<open>a \<in> sem Pr {aa} (inline Pr n l s)\<close> \<open>ver Pr {aa} (inline Pr n l s)\<close> \<open>wf_stmt Pr s\<close> wf_stmt_inline by blast
        moreover have "set (modif ?s') \<subseteq> set (l @ read ?s')" 
          by (simp add: le_supI2 modif_in_read)
        ultimately show "\<sigma> a \<subseteq> set (l @ read (inline Pr n l s))" by auto
      qed

      moreover have "x << x \<and> ver Pr {x} (While b I s)" 
        using R3 \<open>x \<in> ?F\<close> smaller_refl v_singleton by (meson member_filter)
      moreover have "\<exists>\<phi>''\<in>?A. x << \<phi>''"
      proof -
        obtain y where "y \<in> sem Pr {\<phi>'} ?s'" "x << y" using asm3 by auto
        moreover have "\<phi>' \<in> Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} ?s') (fill_set (f A b))" 
          using R2 \<open>\<And>thesis. (\<And>\<phi>''. \<lbrakk>\<phi>'' \<in> A; \<phi>' << \<phi>''\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> fill_set_def
          using \<open>\<phi>'' \<in> f A b\<close> \<phi>''_def(2) by auto
        ultimately show ?thesis  using sem_ver_def[of Pr "fill_set (f A b)" ?s'] 
          by auto
      qed
      have "ver Pr {x} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) \<and> sem Pr {x} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) >> sem Pr {x} (While b I s)"
      proof (rule instantiate_SP[of Pr n "sem_ver Pr (fill_set (f A b)) (inline Pr n l s)" "l @ read ?s'" ?w x x])
        show "SP Pr n (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) (While b I s)" 
          by (simp add: assms(1))
        show "(\<exists>\<phi>''\<in>sem_ver Pr (fill_set (f A b)) (inline Pr n l s). x << \<phi>'') \<and> x << x \<and> ver Pr {x} (While b I s)"
          using \<open>\<exists>\<phi>''\<in>sem_ver Pr (fill_set (f A b)) (inline Pr n l s). x << \<phi>''\<close> calculation(3) by blast
        show "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr (While b I s) \<and>
    SC Pr n (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) (While b I s) \<and>
    no_inter (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) \<and> set (modif (While b I s)) \<subseteq> set (l @ read (inline Pr n l s))"
        proof -
          have "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr (While b I s) \<and> SC Pr n (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) (While b I s)"
            using calculation(1) by blast
          moreover have "set (modif (While b I s)) \<subseteq> set (l @ read ?s')" 
          proof -
            have "set (modif (While b I s)) \<subseteq> set (l @ modif ?s')" 
              using \<open>set (modif s) \<subseteq> set l\<close> by auto
            moreover have "set (modif ?s') \<subseteq> set (read ?s')" 
              using modif_in_read by blast
            ultimately show ?thesis by auto
          qed
          ultimately show ?thesis 
            using \<open>no_inter (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s))\<close> by blast
        qed
      qed
      moreover have "x \<in> F" using asm3 by simp
      ultimately show "ver Pr {x} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) \<and> sem Pr {x} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) >> sem Pr F (While b I s)"
        by (metis bigger_set_singleton singletonD)
    qed

    show ?thesis
    proof -
      have "ver Pr (sem Pr {\<phi>'} ?s') ?w' \<and> sem Pr (sem Pr {\<phi>'} ?s') ?w' >> sem Pr {\<phi>} ?w"
      proof (rule verBiggerI)
        fix x assume "x \<in> sem Pr {\<phi>'} ?s'"
        then obtain y where "y \<in> F \<oplus>\<oplus> {?r}" "y << x" 
          using R2 bigger_set_def by blast
        then obtain ff where "ff \<in> F" "Some y = Some ff \<oplus> Some ?r" 
          using elem_add_set by auto
        then have "ff << y" 
          using smaller_def by blast
        then have "ff << x" 
          using \<open>y << x\<close> smaller_trans by blast
        then have "ff \<in> ?F" 
          using \<open>ff \<in> F\<close> \<open>x \<in> sem Pr {\<phi>'} (inline Pr n l s)\<close> by auto
        then have "ver Pr {ff} ?w' \<and> sem Pr {ff} ?w' >> sem Pr F ?w"
          using R4 bigger_set_forall elem_sem v_singleton by meson
        moreover have "framing Pr (sem_ver Pr (fill_set (f A b)) ?s') ?w'"
          using asm_implied framing_inlined_loop by blast
        moreover have "x \<in> sem_ver Pr (fill_set (f A b)) ?s'"
        proof -
          have "\<phi>'' \<in> f A b"
            using \<open>\<phi>'' \<in> f A b\<close> by auto
          then have "\<phi>' \<in> fill_set (f A b)" 
            using \<phi>''_def(2) elem_fill_set by blast
          then have "\<phi>' \<in> Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} (inline Pr n l s)) (fill_set (f A b))"
            by (simp add: R2)
          then show ?thesis using sem_ver_def \<open>x \<in> sem Pr {\<phi>'} ?s'\<close>
            using elem_sem by blast
        qed
        ultimately have "ver Pr {y} ?w'" using ssafeMono_def
          using \<open>ff << y\<close> framing.simps smaller_refl smono_def ssafeMono_singleton
          by (meson \<open>y << x\<close>)
        moreover have "set (modif ?w') \<inter> \<sigma> ?r = {}" 
        proof -
          have "set (modif ?w') \<inter> \<sigma> ?r \<subseteq> {}"
          proof (rule subsetI)
            fix x assume "x \<in> set (modif ?w') \<inter> \<sigma> (h_comp r V)"
            then have "x \<in> \<sigma> r - set V"
              by (simp add: h_comp_store)
            then have "x \<in> \<sigma> r - (\<sigma> \<phi> \<inter> set (modif s))"
              by (simp add: Int_commute V_def filter_sigma_in)
            moreover have "\<sigma> r \<subseteq> \<sigma> \<phi>"
            proof -
              have "r << \<phi>"
                by (metis \<open>Some \<phi> = Some i \<oplus> Some r\<close> commutative commutative_monoid.smaller_def commutative_monoid_axioms)
              then show ?thesis
                using \<open>Some \<phi> = Some i \<oplus> Some r\<close> store_add by blast
            qed
            moreover have "x \<in> set (modif s)"
            proof -
              have "set (l @ read ?s') \<inter> set (modif ?w') \<subseteq> set (modif ?w)" using asm no_inter_inline_general
                by blast
              then have "set l \<inter> set (modif ?w') \<subseteq> set (modif ?w)" by auto
              moreover have "\<sigma> \<phi>'' \<subseteq> set l" using asm no_inter_def no_inter_single_def
                by (simp add: \<phi>''_def(1))
              moreover have "r << \<phi>''"
                by (metis (full_types) \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>\<phi> << \<phi>''\<close> commutative smaller_def smaller_trans)
              then have "\<sigma> r \<subseteq> \<sigma> \<phi>''"
                using smaller_def store_add by auto
              then have "x \<in> set l"
                using \<open>x \<in> \<sigma> r - set V\<close> calculation(2) by auto
              moreover have "modif s = modif ?w" by simp
              ultimately show ?thesis 
                by (smt IntD1 IntI \<open>x \<in> set (modif (inline Pr n (l @ read (inline Pr n l s)) (While b I s))) \<inter> \<sigma> (h_comp r V)\<close> subset_iff)
            qed
            ultimately show "x \<in> {}"
              by blast
          qed
          then show ?thesis by blast
        qed
        ultimately have "sem Pr {y} ?w' >> sem Pr {ff} ?w' \<oplus>\<oplus> {?r}"
          using \<open>Some y = Some ff \<oplus> Some (h_comp r V)\<close> \<open>framing Pr (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (inline Pr n (l @ read (inline Pr n l s)) (While b I s))\<close> \<open>ver Pr {ff} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) \<and> sem Pr {ff} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) >> sem Pr F (While b I s)\<close> instantiate_framing simple_set_add
          by (smt \<open>Some y = Some ff \<oplus> Some (h_comp r V)\<close> \<open>framing Pr (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (inline Pr n (l @ read (inline Pr n l s)) (While b I s))\<close> \<open>ver Pr {ff} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) \<and> sem Pr {ff} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) >> sem Pr F (While b I s)\<close> \<open>x \<in> sem_ver Pr (fill_set (f A b)) (inline Pr n l s)\<close> \<open>y << x\<close> instantiate_framing simple_set_add)

        moreover have "mono Pr (sem_ver Pr (fill_set (f A b)) ?s') ?w'"
          using \<open>framing Pr (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (inline Pr n (l @ read (inline Pr n l s)) (While b I s))\<close> framing.simps mono_smono by blast
        ultimately have "sem Pr {x} ?w' >> sem Pr {y} ?w'" using smonoOut_def
          using \<open>ver Pr {y} (inline Pr n (l @ read (inline Pr n l s)) (While b I s))\<close> \<open>y << x\<close> mono_smono smaller_refl smonoOut_singleton smono_def 
          using \<open>x \<in> sem_ver Pr (fill_set (f A b)) (inline Pr n l s)\<close> by blast
        moreover have "ver Pr {x} ?w'" 
          using \<open>local.mono Pr (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (inline Pr n (l @ read (inline Pr n l s)) (While b I s))\<close> \<open>ver Pr {y} (inline Pr n (l @ read (inline Pr n l s)) (While b I s))\<close> \<open>x \<in> sem_ver Pr (fill_set (f A b)) (inline Pr n l s)\<close> \<open>y << x\<close> mono_smono smaller_refl smono_def ssafeMono_singleton by blast
        moreover have "sem Pr F ?w >> sem Pr {i_phi} ?w"
          using R3 by blast
        ultimately have "sem Pr {x} ?w' >> sem Pr {i_phi} ?w \<oplus>\<oplus> {?r}"
          by (meson \<open>sem Pr {y} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) >> sem Pr {ff} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) \<oplus>\<oplus> {h_comp r V}\<close> \<open>ver Pr {ff} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) \<and> sem Pr {ff} (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) >> sem Pr F (While b I s)\<close> bigger_set_trans plus_and_bigger_set)
        then have "sem Pr {x} ?w' >> sem Pr {\<phi>} ?w"
          using \<open>sem Pr {i_phi} (While b I s) \<oplus>\<oplus> {h_comp r V} >> sem Pr {\<phi>} (While b I s)\<close> bigger_set_trans by blast
        then show "ver Pr {x} ?w' \<and> sem Pr {x} ?w' >> sem Pr {\<phi>} (While b I s)" 
          using \<open>ver Pr {x} (inline Pr n (l @ read (inline Pr n l s)) (While b I s))\<close> by linarith
      qed
      then have "ver Pr {\<phi>'} (?s' ; ?w')"
        using R2 ver_seq_single by blast
      then have "sem Pr {\<phi>'} (?s' ; ?w') >> sem Pr {\<phi>} ?w"
        using \<open>ver Pr (sem Pr {\<phi>'} (inline Pr n l s)) (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) \<and> sem Pr (sem Pr {\<phi>'} (inline Pr n l s)) (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) >> sem Pr {\<phi>} (While b I s)\<close> sem_seq by presburger
      moreover have "ver Pr {\<phi>'} (Assume b) \<and> sem Pr {\<phi>'} (Assume b) = {\<phi>'}"
        by (simp add: \<open>b \<phi>' = Some True\<close> ver_assume well_defined_assert_def)
      ultimately have "ver Pr {\<phi>'} (Assume b ; ?s' ; ?w') \<and> sem Pr {\<phi>'} (Assume b ; ?s' ; ?w') >> sem Pr {\<phi>} ?w"
        using R2 \<open>ver Pr (sem Pr {\<phi>'} (inline Pr n l s)) (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) \<and> sem Pr (sem Pr {\<phi>'} (inline Pr n l s)) (inline Pr n (l @ read (inline Pr n l s)) (While b I s)) >> sem Pr {\<phi>} (While b I s)\<close> sem_seq_single ver_seq_single by presburger
      moreover have "ver Pr {\<phi>'} (Assume (lnot b)) \<and> sem Pr {\<phi>'} (Assume (lnot b)) = {}"
        by (metis True \<open>b \<phi>' = Some True\<close> \<open>well_defined_assert b \<phi>\<close> can_read_not lnot_false_true(1) sem_assume_false ver_assume well_defined_assert_def)
      ultimately show ?thesis
        by (smt UnE \<open>inline Pr (Suc n) l (While b I s) = stmt.If (Assume b ; inline Pr n l s ; inline Pr n (l @ read (inline Pr n l s)) (While b I s)) (Assume (lnot b))\<close> bigger_set_forall insert_absorb insert_not_empty sem_if_single ver_if)
    qed
  next
    case False
    then have "b \<phi> = Some False"
      by (metis (full_types) \<open>well_defined_assert b \<phi>\<close> not_None_eq well_defined_assert_def)
    then have "b \<phi>' = Some False"
    proof -
      have "ver Pr {\<phi>} (Assume b) \<and> sem Pr {\<phi>} (Assume b) = {}"
        by (simp add: \<open>b \<phi> = Some False\<close> ver_assume well_defined_assert_def)
      moreover have "smono Pr A (Assume b)" using asm_implied wfm_def[of Pr b]
        by blast
      ultimately have "ver Pr {\<phi>'} (Assume b)" using ssafeMono_def[of Pr A "Assume b"] \<phi>''_def asm
        by (meson smono_def ssafeMono_singleton)
      then have "sem Pr {\<phi>'} (Assume b) >> {}" using smonoOut_def[of Pr A "Assume b"] \<phi>''_def asm
        by (metis \<open>smono Pr A (Assume b)\<close> \<open>ver Pr {\<phi>} (Assume b) \<and> sem Pr {\<phi>} (Assume b) = {}\<close> smonoOut_singleton smono_def)
      then have "f {\<phi>'} b = {}"
        using \<open>ver Pr {\<phi>'} (Assume b)\<close> bigger_set_def sem_assume_filter by fastforce
      then have "b \<phi>' \<noteq> Some True"
        using general_same_f by blast
      moreover have "b \<phi>' \<noteq> None" using \<open>ver Pr {\<phi>'} (Assume b)\<close> ver_assume[of Pr \<phi>' b] by simp
      ultimately show ?thesis by auto
    qed
    then have "ver Pr {\<phi>'} (inline Pr (Suc n) l ?w) \<and> sem Pr {\<phi>'} (inline Pr (Suc n) l ?w) = {\<phi>'}"
    proof -
      have "ver Pr {\<phi>'} (Assume b) \<and> ver Pr {\<phi>'} (Assume (lnot b))"
        by (metis \<open>b \<phi>' = Some False\<close> lnot_false_true(2) option.discI ver_assume)
      moreover have "sem Pr {\<phi>'} (Assume b) = {} \<and> sem Pr {\<phi>'} (Assume (lnot b)) = {\<phi>'}"
        by (meson \<open>b \<phi>' = Some False\<close> calculation lnot_false_true(2) sem_assume_false sem_assume_true ver_assume well_defined_assert_def)
      then have "ver Pr {\<phi>'} (Assume b ; ?s' ; ?w')"
        by (metis calculation equals0D v_singleton ver_asso ver_seq)
      then have "ver Pr {\<phi>'} (inline Pr (Suc n) l ?w)"
        by (simp add: calculation ver_if)
      then show ?thesis
        by (metis \<open>inline Pr (Suc n) l (While b I s) = stmt.If (Assume b ; inline Pr n l s ; inline Pr n (l @ read (inline Pr n l s)) (While b I s)) (Assume (lnot b))\<close> \<open>sem Pr {\<phi>'} (Assume b) = {} \<and> sem Pr {\<phi>'} (Assume (lnot b)) = {\<phi>'}\<close> \<open>ver Pr {\<phi>'} (Assume b ; inline Pr n l s ; inline Pr n (l @ read (inline Pr n l s)) (While b I s))\<close> empty_set_goes_empty f_inclusion sem_assume_filter sem_if_single subset_Un_eq ver_seq_single)
    qed
    moreover have "{\<phi>'} >> F \<oplus>\<oplus> {?r}" using asm
      by (metis (no_types, hide_lams) \<open>{\<phi>} >> F \<oplus>\<oplus> {h_comp r V}\<close> bigger_set_forall bigger_set_trans elem_add_set insertI1 rel_bigger_add_set smaller_def)
    then have "{\<phi>'} >> f (F \<oplus>\<oplus> {?r}) (lnot b)"
    proof -
      obtain ff where "ff \<in> F \<oplus>\<oplus> {?r}" "ff << \<phi>'"
        using \<open>{\<phi>'} >> F \<oplus>\<oplus> {?r}\<close> bigger_set_def by auto
      then have "ver Pr {ff} (Assume (lnot b))" 
        using \<open>f (F \<oplus>\<oplus> {h_comp r V}) (lnot b) \<subseteq> sem Pr {\<phi>} (While b I s) \<and> ver Pr (F \<oplus>\<oplus> {h_comp r V}) (Assume (lnot b))\<close> v_singleton by blast
      moreover have "smonoOut Pr A (Assume (lnot b))" using asm_implied
        using smono_def wfm_def by blast
      ultimately have "sem Pr {\<phi>'} (Assume (lnot b)) >> sem Pr {ff} (Assume (lnot b))"
        using \<open>ff << \<phi>'\<close> \<phi>''_def(1) \<phi>''_def(2) smonoOut_singleton by blast
      have "lnot b ff = Some True"
      proof -
        have "lnot b ff = lnot b \<phi>'"
        proof (rule assume_mono_same_b)
          show "mono Pr A (Assume (lnot b))" using asm_implied wfm_def 
            using mono_smono by blast
          show "lnot b ff = Some False \<or> lnot b \<phi>' = Some True" 
            by (simp add: \<open>b \<phi>' = Some False\<close> lnot_false_true(2))
          show "lnot b ff \<noteq> None" using \<open>ver Pr {ff} (Assume (lnot b))\<close> 
            by (simp add: ver_assume)
          show "ff << \<phi>'" 
            by (simp add: \<open>ff << \<phi>'\<close>)
          show "\<phi>' << \<phi>''" 
            by (simp add: \<phi>''_def(2))
          show "\<phi>'' \<in> A" 
            by (simp add: \<phi>''_def(1))
        qed
        then show ?thesis 
          by (simp add: \<open>b \<phi>' = Some False\<close> lnot_false_true(2))
      qed
      then have "ff \<in> f (F \<oplus>\<oplus> {?r}) (lnot b)" using f_def \<open>ff \<in> F \<oplus>\<oplus> {?r}\<close>
        by simp
      then show ?thesis
        using \<open>ff << \<phi>'\<close> bigger_set_def by blast
    qed
    then show ?thesis 
      using \<open>f (F \<oplus>\<oplus> {h_comp r V}) (lnot b) \<subseteq> sem Pr {\<phi>} (While b I s) \<and> ver Pr (F \<oplus>\<oplus> {h_comp r V}) (Assume (lnot b))\<close> bigger_set_trans calculation subset_smaller by presburger
  qed
qed

lemma same_havoc:
  assumes "ver Pr {x} (Havoc V)"
  shows "x \<in> sem Pr {x} (Havoc V)"
proof -
  have "set V \<subseteq> \<sigma> x" 
    using assms ver_havoc by blast
  then obtain hv where "hv \<in> h V" "hv << x" 
    by (meson bigger_set_def h_bigger insertI1)
  then obtain xx where "Some xx = Some (h_comp x V) \<oplus> Some hv" 
  proof -
    assume "\<And>xx. Some xx = Some (h_comp x V) \<oplus> Some hv \<Longrightarrow> thesis"
    moreover
    { assume "Some hv \<oplus> Some x \<noteq> None"
      then have "\<exists>z. Some hv \<oplus> (z \<oplus> Some (h_comp x V)) \<noteq> None"
        by (metis (no_types) commutative h_comp_sum)
      then have "\<exists>a. Some a = Some hv \<oplus> Some (h_comp x V)"
        by (metis (no_types) associative commutative plus.elims) }
    ultimately show ?thesis
      by (metis (no_types) \<open>hv << x\<close> \<open>hv \<in> h V\<close> commutative h_pure plus.elims pure_smaller_ok)
  qed
  then have "xx = x"
  proof -
    have "C xx = C x" 
      by (metis \<open>Some xx = Some (h_comp x V) \<oplus> Some hv\<close> \<open>hv \<in> h V\<close> c_add h_comp_only_pure h_pure neutral option.sel pure_c s_C_def)
    moreover have "|xx| = |x|"
    proof -
      have "|h_comp x V| << |x|"
        using h_comp_smaller smaller_core_comp by blast
      moreover have "|hv| << |x|" 
        using \<open>hv << x\<close> smaller_core_comp by blast
      ultimately have "|xx| << |x|" 
        by (smt \<open>Some xx = Some (h_comp x V) \<oplus> Some hv\<close> \<open>hv << x\<close> \<open>hv \<in> h V\<close> add_trans core_properties(2) h_comp_smaller h_pure not_pure_core pure_smaller_ok smaller_core_comp)
      moreover have "\<sigma> |xx| = \<sigma> |x|"
      proof -
        have "\<sigma> xx = (\<sigma> x - set V) \<union> set V" 
          using \<open>Some xx = Some (h_comp x V) \<oplus> Some hv\<close> \<open>hv \<in> h V\<close> h_comp_store h_store store_add by auto
        then show ?thesis 
          using \<open>set V \<subseteq> \<sigma> x\<close>
          using store_pure by auto
      qed
      ultimately show ?thesis
        by (simp add: core_properties(1) pure_is_exactly_store_variant)
    qed
    ultimately show ?thesis 
      by (simp add: \<open>C xx = C x\<close> \<open>|xx| = |x|\<close> properties_c(1))
  qed
  then show ?thesis 
    using \<open>Some xx = Some (h_comp x V) \<oplus> Some hv\<close> \<open>hv \<in> h V\<close> assms sem_havoc set_add_elem_reci by blast
qed

lemma soundness_invariant:
  "SP Pr n A l s"
proof (induction arbitrary: A rule: inline.induct)
  case (1 Pr l y m x)
  show ?case
  proof (cases "get_method Pr m = None")
    case True
    then show ?thesis by (simp add: SP_def)
  next
    case False
    then have "inline Pr 0 l (MethodCall y m x) = Assume lfalse" by simp
    show ?thesis
    proof (rule SP_I)
      fix \<phi> \<phi>'
      assume asm: "ver_program Pr \<and>
       wf_program Pr \<and>
       wf_stmt Pr (MethodCall y m x) \<and>
       SC Pr 0 A l (MethodCall y m x) \<and> no_inter A l \<and> set (modif (MethodCall y m x)) \<subseteq> set l \<and> (\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} (MethodCall y m x)"
      then have "ver Pr {\<phi>'} (inline Pr 0 l (MethodCall y m x))"
        by (simp add: lfalse_def ver_assume)
      then show "ver Pr {\<phi>'} (inline Pr 0 l (MethodCall y m x)) \<and> sem Pr {\<phi>'} (inline Pr 0 l (MethodCall y m x)) >> sem Pr {\<phi>} (MethodCall y m x)"
        by (metis \<open>inline Pr 0 l (MethodCall y m x) = Assume lfalse\<close> assume_false_sem equals0D strongerI)
    qed
  qed
next
  case (2 Pr l b I s)
  have "inline Pr 0 l (While b I s) = Assume (lnot b)" by simp
  show ?case
  proof (rule SP_I)

    fix \<phi> \<phi>'
    assume asm: "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr (While b I s) \<and> SC Pr 0 A l (While b I s) \<and> no_inter A l
  \<and> set (modif (While b I s)) \<subseteq> set l \<and> (\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} (While b I s)"
    then have "ver Pr {\<phi>'} (Assume (lnot b)) \<and> sem Pr {\<phi>'} (Assume (lnot b)) >> sem Pr {\<phi>} (While b I s)"
    proof -
      have "smono Pr A (Assume (lnot b))" using asm by simp

      moreover have "ver Pr {\<phi>} (Assume b) \<and> (lnot b \<phi> = Some True \<longrightarrow> \<phi> \<in> sem Pr {\<phi>} (While b I s))"
      proof -
        have "ver Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I ; Assume (lnot b))" using asm ver_loop
          by simp
        moreover have "wf_assert I" using asm by simp
        ultimately have "{\<phi>} >> Inh I" 
          by (simp add: supported_intui_exhale ver_seq)
        then obtain i r where "i \<in> Inh I" "Some \<phi> = Some i \<oplus> Some r" 
          using bigger_set_def smaller_def by auto
        then obtain core_i_phi where "Some core_i_phi = s_core i \<oplus> Some r" 
          by (metis Option.is_none_def associative commutative decompo_new_plus defined_def definedness(3) is_none_code(2) option.discI option.expand option.inject option.sel plus.simps(2) s_C_def)
        then have "core_i_phi \<in> sem Pr {\<phi>} (Exhale I)" 
          using \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>i \<in> Inh I\<close> \<open>wf_assert I\<close> \<open>{\<phi>} >> Inh I\<close> exhale_elem supported_intui_exhale by blast
        moreover have "ver Pr {core_i_phi} (Havoc (filter_sigma \<phi> (modif s)))" 
          using \<open>wf_assert I\<close> \<open>{\<phi>} >> Inh I\<close> calculation filter_sigma_in store_same_pred_supp_exhale supported_intui_exhale ver_havoc by fastforce
        ultimately have "core_i_phi \<in> sem Pr {core_i_phi} (Havoc (filter_sigma \<phi> (modif s)))" 
          using same_havoc by blast
        then have "core_i_phi \<in> sem Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)))" 
          by (metis (no_types, lifting) \<open>core_i_phi \<in> sem Pr {\<phi>} (Exhale I)\<close> \<open>ver Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I ; Assume (lnot b))\<close> elem_sem sem_seq ver_seq)
        then have "ver Pr {core_i_phi} (Inhale I)" 
          by (meson \<open>ver Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I ; Assume (lnot b))\<close> v_singleton ver_seq)
        then have "\<phi> \<in> sem Pr {core_i_phi} (Inhale I)" 
          by (smt \<open>Some \<phi> = Some i \<oplus> Some r\<close> \<open>Some core_i_phi = s_core i \<oplus> Some r\<close> \<open>i \<in> Inh I\<close> associative commutative core_properties(1) core_properties(2) elem_add_set pure_smaller_ok s_core_def sem_inhale singletonI ver_inhale)
        then have "\<phi> \<in> sem Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I)" 
          by (metis \<open>core_i_phi \<in> sem Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)))\<close> \<open>ver Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I ; Assume (lnot b))\<close> elem_sem sem_seq ver_seq)
        then have "ver Pr {\<phi>} (Assume (lnot b))" 
          by (meson \<open>ver Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I ; Assume (lnot b))\<close> v_singleton ver_seq)
        then have "ver Pr {\<phi>} (Assume b)" 
          by (meson can_read_not ver_assume well_defined_assert_def)
        then have "lnot b \<phi> = Some True \<Longrightarrow> \<phi> \<in> sem Pr {\<phi>} (While b I s)"
        proof -
          assume asm2: "lnot b \<phi> = Some True"
          then have "\<phi> \<in> sem Pr {\<phi>} (Assume (lnot b))" 
            by (simp add: well_defined_assert_def)
          then have "\<phi> \<in> sem Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I ; Assume (lnot b))" 
            by (metis \<open>\<phi> \<in> sem Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I)\<close> \<open>ver Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I ; Assume (lnot b))\<close> elem_sem sem_seq)
          moreover have "sem Pr {\<phi>} (While b I s) = sem Pr {\<phi>} (Exhale I ; Havoc (filter_sigma \<phi> (modif s)) ; Inhale I ; Assume (lnot b))" using asm sem_loop
            by blast
          ultimately show "\<phi> \<in> sem Pr {\<phi>} (While b I s)" by simp
        qed
        then show ?thesis 
          using \<open>ver Pr {\<phi>} (Assume b)\<close> by blast
      qed

      moreover obtain \<phi>'' where "\<phi>'' \<in> A" "\<phi>' << \<phi>''" using asm by blast
      ultimately have "ver Pr {\<phi>'} (Assume (lnot b))" using asm using ssafeMono_def
        by (smt can_read_not semantics.simps(2) singletonI smono_def ssafeMono_singleton ver_assume ver_def well_defined_assert_def)
      then have "sem Pr {\<phi>'} (Assume (lnot b)) >> sem Pr {\<phi>} (While b I s)"
      proof (cases "lnot b \<phi>' = Some True")
        case True
        then have "sem Pr {\<phi>'} (Assume (lnot b)) = {\<phi>'}" 
          by (simp add: well_defined_assert_def)
        moreover have "lnot b \<phi> = Some True"
        proof -
          have "ver Pr {\<phi>} (Assume b)" 
            using \<open>ver Pr {\<phi>} (Assume b) \<and> (lnot b \<phi> = Some True \<longrightarrow> \<phi> \<in> sem Pr {\<phi>} (While b I s))\<close> by blast
          then have "lnot b \<phi> \<noteq> None" 
            by (simp add: lnot_def ver_assume)
          moreover have "mono Pr A (Assume (lnot b))" 
            by (simp add: \<open>smono Pr A (Assume (lnot b))\<close> mono_smono)
          ultimately show ?thesis using assume_mono_same_b[of Pr A "lnot b" \<phi> \<phi>' \<phi>''] True 
            using \<open>\<phi>' << \<phi>''\<close> \<open>\<phi>'' \<in> A\<close> asm by auto
        qed
        then show ?thesis using asm 
          by (metis \<open>ver Pr {\<phi>} (Assume b) \<and> (lnot b \<phi> = Some True \<longrightarrow> \<phi> \<in> sem Pr {\<phi>} (While b I s))\<close> bigger_set_def calculation singletonD)
      next
        case False
        then have "sem Pr {\<phi>'} (Assume (lnot b)) = {}"
          by (meson \<open>ver Pr {\<phi>'} (Assume (lnot b))\<close> semantics.simps(2) singleton_semantics ver_assume well_defined_assert_def)
        then show ?thesis
          using bigger_set_def by auto
      qed
      then show ?thesis
        using \<open>ver Pr {\<phi>'} (Assume (lnot b))\<close> by blast
    qed
    then show "ver Pr {\<phi>'} (inline Pr 0 l (While b I s)) \<and> sem Pr {\<phi>'} (inline Pr 0 l (While b I s)) >> sem Pr {\<phi>} (While b I s)"
      using \<open>inline Pr 0 l (While b I s) = Assume (lnot b)\<close> by argo
  qed
next
  case (3 Pr n l y m x)
  define r where "r = get_method Pr m"
  then show ?case
  proof (cases "r = None")
    case True
    then show ?thesis
      using SP_def r_def by force
  next
    case False
    then obtain args rets P Q s where "get_method Pr m = Some (m, args, rets, P, Q, s)"
      using get_method_same_name r_def by fastforce
    then show ?thesis using method_inlining_induct[of Pr n A]"3.IH"
      by (metis method_inlining_induct not_None_eq option.sel r_def)
  qed
next
  case (4 Pr n l b I s)
  show ?case
  proof (rule loop_inling_induct)
    show "SP Pr n (sem_ver Pr (fill_set (f A b)) (inline Pr n l s)) (l @ read (inline Pr n l s)) (While b I s)" 
      using "4.IH"(3) by blast
    show "SP Pr n (f A b) l s"
      by (simp add: "4.IH"(1))
  qed
next
  case (5 Pr n l s1 s2)
  define s where "s = Seq s1 s2"
  show ?case
  proof (rule SP_I)
    fix \<phi> \<phi>'
    assume asm: "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr (s1 ; s2) \<and> SC Pr n A l (s1 ; s2) \<and> no_inter A l
  \<and> set (modif (s1 ; s2)) \<subseteq> set l \<and> (\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} (s1 ; s2)"
    then show "ver Pr {\<phi>'} (inline Pr n l (s1 ; s2)) \<and> sem Pr {\<phi>'} (inline Pr n l (s1 ; s2)) >> sem Pr {\<phi>} (s1 ; s2)"
    proof (cases "inlinable s")
      case True
      have "ver Pr {\<phi>'} (inline Pr n l s1) \<and> sem Pr {\<phi>'} (inline Pr n l s1) >> sem Pr {\<phi>} s1"
      proof -
        have "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr s1 \<and> no_inter A l \<and> \<phi> << \<phi>'" using asm
          using wf_stmt.simps(1) by blast
        moreover have "SC Pr n A l s1"
          using SC_inlinable_implies_seq(1) True asm s_def by blast
        moreover have "set (modif s1) \<subseteq> set l" using asm by simp
        moreover have "(\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> ver Pr {\<phi>} s1" using asm ver_seq by blast
        ultimately show ?thesis
          using "5.IH"(1) SP_def[of Pr n A l s1] asm by blast
      qed

      moreover have res_a: "ver Pr {\<phi>'} (inline Pr n l s1) \<and> sem Pr {\<phi>'} (inline Pr n l s1) >> sem Pr {\<phi>} s1"
      proof -
        have "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr s1 \<and> no_inter A l \<and> \<phi> << \<phi>'" using asm
          using wf_stmt.simps(1) by blast
        moreover have "SC Pr n A l s1"
          using SC_inlinable_implies_seq(1) True asm s_def by blast
        moreover have "set (modif s1) \<subseteq> set l" using asm by simp
        moreover have "(\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> ver Pr {\<phi>} s1" using asm ver_seq by blast
        ultimately show ?thesis
          using "5.IH"(1) SP_def[of Pr n A l s1] asm by blast
      qed

      let ?A = "sem_ver Pr (fill_set A) (inline Pr n l s1)"
      define new_l where "new_l = l @ read (inline Pr n l s1)"
      then have "SP Pr n ?A new_l s2" using "5.IH"(2) by blast
      then have res_b: "ver Pr (sem Pr {\<phi>'} (inline Pr n l s1)) (inline Pr n new_l s2) \<and> sem Pr (sem Pr {\<phi>'} (inline Pr n l s1)) (inline Pr n new_l s2) >> sem Pr (sem Pr {\<phi>} s1) s2"
      proof -
        have "\<And>xx. xx \<in> sem Pr {\<phi>'} (inline Pr n l s1) \<Longrightarrow> ver Pr {xx} (inline Pr n new_l s2) \<and>
                sem Pr ({xx}) (inline Pr n new_l s2) >> sem Pr (sem Pr {\<phi>} s1) s2"
        proof -
          fix xx'
          assume new_asm: "xx' \<in> sem Pr {\<phi>'} (inline Pr n l s1)"

          have "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr s2"
            using wf_stmt.simps(1) asm by simp
          moreover have "no_inter ?A new_l"
          proof -
            have "no_inter A l" using asm by simp
            have "no_inter (fill_set A) l"
            proof (rule no_inter_I)
              fix a assume "a \<in> fill_set A"
              then obtain aa where "aa \<in> A" "a << aa"
                using elem_fill_set by blast
              then have "\<sigma> a \<subseteq> \<sigma> aa"
                using commutative_monoid.smaller_def commutative_monoid_axioms store_add by fastforce
              then show "\<sigma> a \<subseteq> set l"
                using \<open>aa \<in> A\<close> \<open>no_inter A l\<close> no_inter_def no_inter_single_def by auto
            qed
            show ?thesis
            proof (rule no_inter_I)
              let ?s1 = "inline Pr n l s1"
              fix a assume "a \<in> sem_ver Pr (fill_set A) ?s1"
              then obtain aa where "aa \<in> (Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} ?s1) (fill_set A))" "a \<in> sem Pr {aa} ?s1"
                using sem_ver_def by auto
              then have "aa \<in> fill_set A \<and> ver Pr {aa} (inline Pr n l s1)" by simp
              moreover have "\<sigma> a \<subseteq> \<sigma> aa \<union> set (modif ?s1)" using store_modif_sem[of Pr ?s1 aa a]
                asm using \<open>a \<in> sem Pr {aa} (inline Pr n l s1)\<close> calculation wf_stmt.simps(1) wf_stmt_inline by blast
              ultimately show "\<sigma> a \<subseteq> set new_l" 
                by (smt Un_mono \<open>no_inter (fill_set A) l\<close> modif_in_read new_l_def no_inter_def no_inter_single_def set_append subset_UnE subset_trans)
            qed
          qed
          moreover have "SC Pr n ?A new_l s2"
            using SC_inlinable_implies_seq(2) True asm s_def new_l_def by blast
          moreover have "set (modif s2) \<subseteq> set new_l" using asm
            using new_l_def by auto
  
          obtain xx where "xx << xx'" "xx \<in> sem Pr {\<phi>} s1" using new_asm res_a
            using bigger_set_def by blast
          then have "ver Pr {xx} s2" using asm ver_seq
            by (meson v_singleton)
  
          moreover have "xx' \<in> ?A" using new_asm
          proof -
            have "\<phi>' \<in> fill_set A"
            proof -
              obtain \<phi>'' where "\<phi>' << \<phi>''" "\<phi>'' \<in> A" using asm by blast
              then show ?thesis
                using elem_fill_set by blast
            qed
            moreover have "ver Pr {\<phi>'} (inline Pr n l s1)"
              using res_a by linarith
            ultimately have "\<phi>' \<in> Set.filter (\<lambda>\<phi>. ver Pr {\<phi>} (inline Pr n l s1)) (fill_set A)"
              by simp
            then show ?thesis using sem_ver_def 
              using elem_sem new_asm by blast
          qed
  
          then have "(\<exists>\<phi>''\<in>?A. xx' << \<phi>'')" using asm
            using smaller_refl by blast


          then show "ver Pr {xx'} (inline Pr n new_l s2) \<and> sem Pr {xx'} (inline Pr n new_l s2) >> sem Pr (sem Pr {\<phi>} s1) s2"
            using SP_def[of Pr n ?A new_l s2] \<open>SP Pr n ?A new_l s2\<close>
            by (smt \<open>set (modif s2) \<subseteq> set new_l\<close> \<open>xx << xx'\<close> \<open>xx \<in> sem Pr {\<phi>} s1\<close> bigger_set_singleton calculation(1) calculation(2) calculation(3) calculation(4) singletonD)
        qed


        then show ?thesis
          by (meson bigger_set_forall elem_sem v_singleton)
      qed

      moreover have inl: "inline Pr n l (s1 ; s2) = inline Pr n l s1 ; inline Pr n new_l s2" using new_l_def
        by (meson inline.simps(5))
      then have "ver Pr {\<phi>'} (inline Pr n l (s1 ; s2))" using res_a res_b ver_seq by simp

      then have "sem Pr {\<phi>'} (inline Pr n l (s1 ; s2)) >> sem Pr {\<phi>} (s1 ; s2)"
      proof -
        have "sem Pr {\<phi>'} (inline Pr n l (s1 ; s2)) >> sem Pr (sem Pr {\<phi>} s1) s2"
          using \<open>ver Pr {\<phi>'} (inline Pr n l (s1 ; s2))\<close> inl res_b sem_seq by force
        moreover have "sem Pr (sem Pr {\<phi>} s1) s2 = sem Pr {\<phi>} (s1 ; s2)" using asm ver_seq sem_seq by blast
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis using res_a 
        using \<open>ver Pr {\<phi>'} (inline Pr n l (s1 ; s2))\<close> by blast
    next
      case False
      then show ?thesis
        by (metis SC.elims(2) asm not_inlinable_id s_def smonoOut_singleton smono_def ssafeMono_singleton)
    qed
  qed
next
  case (6 Pr n l s1 s2)
  define s where "s = If s1 s2"
  let ?s1 = "inline Pr n l s1"
  let ?s2 = "inline Pr n l s2"
  show ?case
  proof (rule SP_I)
    fix \<phi> \<phi>'
    assume asm: "ver_program Pr \<and> wf_program Pr \<and> wf_stmt Pr (stmt.If s1 s2) \<and> SC Pr n A l (stmt.If s1 s2)
  \<and> no_inter A l \<and> set (modif (stmt.If s1 s2)) \<subseteq> set l \<and> (\<exists>\<phi>''\<in>A. \<phi>' << \<phi>'') \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} (stmt.If s1 s2)"
    then show "ver Pr {\<phi>'} (inline Pr n l (stmt.If s1 s2)) \<and> sem Pr {\<phi>'} (inline Pr n l (stmt.If s1 s2)) >> sem Pr {\<phi>} (stmt.If s1 s2)"
    proof (cases "inlinable s")
      case True
      then have "wf_stmt Pr s1 \<and> SC Pr n A l s1 \<and> set (modif s1) \<subseteq> set l \<and> ver Pr {\<phi>} s1" using asm ver_if
        by (simp add: s_def)
      then have "ver Pr {\<phi>'} ?s1 \<and> sem Pr {\<phi>'} ?s1 >> sem Pr {\<phi>} s1"
        using "6.IH"(1) SP_def asm by auto
      moreover have "wf_stmt Pr s2 \<and> SC Pr n A l s2 \<and> set (modif s2) \<subseteq> set l \<and> ver Pr {\<phi>} s2" using asm ver_if True
        using s_def by auto
      then have "ver Pr {\<phi>'} ?s2 \<and> sem Pr {\<phi>'} ?s2 >> sem Pr {\<phi>} s2"
        using "6.IH"(2) SP_def asm by auto
      ultimately show ?thesis
        using asm bigger_set_union sem_if_single ver_if by auto
    next
      case False
      then show ?thesis
        by (metis SC.elims(2) asm not_inlinable_id s_def smonoOut_singleton smono_def ssafeMono_singleton)
    qed
  qed
qed (simp_all add: soundness_invariant_not_inlinable)

fun same_not_annotated_stmt :: "('a, 'b, 'c) stmt \<Rightarrow> ('a, 'b, 'c) stmt \<Rightarrow> bool" where
  "same_not_annotated_stmt (If s1a s1b) (If s2a s2b) \<longleftrightarrow> same_not_annotated_stmt s1a s2a \<and> same_not_annotated_stmt s1b s2b"
| "same_not_annotated_stmt (s1a ; s1b) (s2a ; s2b) \<longleftrightarrow> same_not_annotated_stmt s1a s2a \<and> same_not_annotated_stmt s1b s2b"
| "same_not_annotated_stmt (While b1 I1 s1) (While b2 I2 s2) \<longleftrightarrow> (b1 = b2 \<and> same_not_annotated_stmt s1 s2)"
| "same_not_annotated_stmt s1 s2 \<longleftrightarrow> s1 = s2"

fun same_not_annotated_programs :: "('a, 'b, 'c) program \<Rightarrow> ('a, 'b, 'c) program \<Rightarrow> bool" where
  "same_not_annotated_programs [] [] \<longleftrightarrow> True"
| "same_not_annotated_programs ((m1, args1, rets1, P1, Q1, s1) # Pr1) ((m2, args2, rets2, P2, Q2, s2) # Pr2)
  \<longleftrightarrow> m1 = m2 \<and> args1 = args2 \<and> rets1 = rets2 \<and> same_not_annotated_stmt s1 s2 \<and> same_not_annotated_programs Pr1 Pr2"
| "same_not_annotated_programs _ _ = False"

lemma method_not_found_exhale_false:
  assumes "get_method Pr m = None"
  shows "inline Pr (Suc n) l (MethodCall y m x) = Exhale lfalse"
  using assms inline.simps(3)
  by simp

thm same_not_annotated_programs.induct[of "\<lambda>Pr1 Pr2. get_method Pr1 m = None \<longrightarrow> get_method Pr2 m = None"]

lemma get_method_same_program_none:
  assumes "same_not_annotated_programs Pr1 Pr2"
      and "get_method Pr1 m = None"
    shows "get_method Pr2 m = None"
proof -
  have "same_not_annotated_programs Pr1 Pr2 \<and> get_method Pr1 m = None \<longrightarrow> get_method Pr2 m = None"
    by (induct rule: same_not_annotated_programs.induct[of "\<lambda>Pr1 Pr2. same_not_annotated_programs Pr1 Pr2 \<and> get_method Pr1 m = None \<longrightarrow> get_method Pr2 m = None"])
    auto
  then show ?thesis 
    using assms(1) assms(2) by blast
qed

lemma get_method_same_program_some:
  assumes "same_not_annotated_programs Pr1 Pr2"
      and "get_method Pr1 m = Some (m, args, rets, P1, Q1, s1)"
    shows "\<exists>P2 Q2 s2. get_method Pr2 m = Some (m, args, rets, P2, Q2, s2) \<and> same_not_annotated_stmt s1 s2"
proof -
  have "same_not_annotated_programs Pr1 Pr2 \<and> get_method Pr1 m = Some (m, args, rets, P1, Q1, s1) \<longrightarrow> 
  (\<exists>P2 Q2 s2. get_method Pr2 m = Some (m, args, rets, P2, Q2, s2) \<and> same_not_annotated_stmt s1 s2)"
    by (induct rule: same_not_annotated_programs.induct[of "\<lambda>Pr1 Pr2. same_not_annotated_programs Pr1 Pr2 \<and> get_method Pr1 m = Some (m, args, rets, P1, Q1, s1) \<longrightarrow> 
  (\<exists>P2 Q2 s2. get_method Pr2 m = Some (m, args, rets, P2, Q2, s2) \<and> same_not_annotated_stmt s1 s2)"])
    auto
  then show ?thesis 
    using assms(1) assms(2) by blast
qed

lemma read_same_annotated:
  "same_not_annotated_stmt s1 s2 \<longrightarrow> modif s1 = modif s2"
  by (induct rule: same_not_annotated_stmt.induct) auto

lemma rename_same_annotated:
  "same_not_annotated_stmt s1 s2 \<longrightarrow> same_not_annotated_stmt (rename s1 t) (rename s2 t)"
  by (induction rule: same_not_annotated_stmt.induct[of "\<lambda>s1 s2. same_not_annotated_stmt s1 s2 \<longrightarrow> same_not_annotated_stmt (rename s1 t) (rename s2 t)"])
    auto

lemma same_not_annotated_same_inlined:
  assumes "same_not_annotated_programs Pr1 Pr2"
      and "same_not_annotated_stmt s1 s2"
    shows "inline Pr1 n V s1 = inline Pr2 n V s2"
proof -
  have "\<forall>s2. same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt s1 s2 \<longrightarrow> inline Pr1 n V s1 = inline Pr2 n V s2"
  proof (induction rule: inline.induct[of "\<lambda>Pr1 n V s1. \<forall>s2. same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt s1 s2 \<longrightarrow> inline Pr1 n V s1 = inline Pr2 n V s2"])
    case (2 Pr1 l b I1 s)
    let ?s1 = "While b I1 s"
    have "\<And>Pr2 s2. same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2 \<Longrightarrow> inline Pr1 0 l ?s1 = inline Pr2 0 l s2"
    proof -
      fix Pr2 s2 assume "same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2"
      then have "\<exists>I' s'. s2 = While b I' s'" by (cases s2) auto
      then show "inline Pr1 0 l (While b I1 s) = inline Pr2 0 l s2" by auto
    qed
    then show ?case by simp
  next
    case (3 Pr1 n l y m x)
    let ?s1 = "MethodCall y m x"
    have "\<And>s2. same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2 \<Longrightarrow> inline Pr1 (Suc n) l ?s1 = inline Pr2 (Suc n) l s2"
    proof -
      fix s2 assume asm: "same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2"
      then have s2_def: "s2 = MethodCall y m x"
        by (cases s2) auto
      then show "inline Pr1 (Suc n) l ?s1 = inline Pr2 (Suc n) l s2"
      proof (cases "get_method Pr1 m = None")
        case True
        then have "get_method Pr2 m = None" 
          using asm get_method_same_program_none by blast
        then show ?thesis using method_not_found_exhale_false True 
          by (simp add: \<open>s2 = MethodCall y m x\<close>)
      next
        case False
        then obtain rets args P1 Q1 s1 where "get_method Pr1 m = Some (m, args, rets, P1, Q1, s1)" 
          using get_method_same_name by fastforce
        then obtain P2 Q2 s2 where "get_method Pr2 m = Some (m, args, rets, P2, Q2, s2)" "same_not_annotated_stmt s1 s2"
          using asm get_method_same_program_some by blast
        then have "same_not_annotated_stmt (rename s1 (args @ rets, x @ y, l, modif s1)) (rename s2 (args @ rets, x @ y, l, modif s2))"
          (is "same_not_annotated_stmt ?s1 ?s2")
          using read_same_annotated rename_same_annotated by auto
  
        let ?new_s1 = "rename s1 (args @ rets, x @ y, l, modif s1)"
        let ?new_l1 = "l @ modif ?new_s1"
        let ?new_s2 = "rename s2 (args @ rets, x @ y, l, modif s2)"
  
        have "inline Pr1 n ?new_l1 ?new_s1 = inline Pr2 n ?new_l1 ?new_s2"
          using 3[of _ _ _ _ _ _ _ _ _ _ _ _ ?new_s1] 
          by (simp add: \<open>get_method Pr1 m = Some (m, args, rets, P1, Q1, s1)\<close> \<open>same_not_annotated_stmt (rename s1 (args @ rets, x @ y, l, modif s1)) (rename s2 (args @ rets, x @ y, l, modif s2))\<close> asm)
        then show ?thesis 
          using \<open>get_method Pr1 m = Some (m, args, rets, P1, Q1, s1)\<close> \<open>get_method Pr2 m = Some (m, args, rets, P2, Q2, s2)\<close> \<open>same_not_annotated_stmt (rename s1 (args @ rets, x @ y, l, modif s1)) (rename s2 (args @ rets, x @ y, l, modif s2))\<close> get_method_inlined read_same_annotated s2_def by auto
       qed
     qed
     then show ?case by simp
  next
    case (4 Pr1 n l b I s)
    let ?s1 = "While b I s"
    have "\<And>s2. same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2 \<Longrightarrow> inline Pr1 (Suc n) l ?s1 = inline Pr2 (Suc n) l s2"
    proof -
      fix s2 assume asm: "same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2"
      then have "\<exists>I' s'. s2 = While b I' s'"
        by (cases s2) auto
      then obtain I' s' where "s2 = While b I' s'" by blast
      then have "same_not_annotated_stmt s s'" 
        using asm by auto
      then have "inline Pr1 n l s = inline Pr2 n l s'"
        using 4 asm by blast
      moreover have "inline Pr1 n (l @ read (inline Pr1 n l s)) (While b I s) = inline Pr2 n (l @ read (inline Pr1 n l s)) s2"
        using 4 asm by blast
      moreover have "inline Pr1 (Suc n) l (While b I s) = stmt.If (Assume b ; inline Pr1 n l s ; inline Pr1 n (l @ read (inline Pr1 n l s)) (While b I s)) (Assume (lnot b))"
        by simp
      moreover have "read (inline Pr1 n l s) = read (inline Pr2 n l s')" 
        using calculation(1) by auto
      ultimately show "inline Pr1 (Suc n) l ?s1 = inline Pr2 (Suc n) l s2"
        using 4 by (simp add: \<open>s2 = While b I' s'\<close>)
    qed
    then show ?case by simp
next
  case (5 Pr1 n l a b)
  let ?s1 = "a ; b"
  have "\<And>s2. same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2 \<Longrightarrow> inline Pr1 n l ?s1 = inline Pr2 n l s2"
  proof -
      fix s2 assume asm0: "same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2"
      have "\<exists>s2a s2b. s2 = s2a ; s2b"
      proof (rule ccontr)
        assume asm: "\<nexists>s2a s2b. s2 = s2a ; s2b"
        then have "a ; b \<noteq> s2" by auto
        then have "\<not> same_not_annotated_stmt (a ; b) s2"
        proof (cases s2)
          case (Seq x61 x62)
          then show ?thesis using asm by blast
        qed (simp_all)
        then show "False" using asm0 by simp
      qed
      then obtain s2a s2b where "s2 = s2a ; s2b" by blast
      then have "inline Pr1 n l a = inline Pr2 n l s2a" 
        using "5.hyps"(1) asm0 same_not_annotated_stmt.simps(2) by blast
      moreover have "inline Pr1 n (l @ read (inline Pr1 n l a)) b = inline Pr2 n (l @ read (inline Pr1 n l a)) s2b"
        using "5.hyps"(2) \<open>s2 = s2a ; s2b\<close> asm0 by auto
      moreover have "l @ read (inline Pr1 n l a) = l @ read (inline Pr2 n l s2a)"
        by (simp add: calculation(1))
      moreover have "inline Pr1 n l ?s1 = inline Pr1 n l a ; inline Pr1 n (l @ read (inline Pr1 n l a)) b"
        using inline.simps(5)[of Pr1 n l a b] by meson
      moreover have "inline Pr2 n l s2 = inline Pr2 n l s2a ; inline Pr2 n (l @ read (inline Pr2 n l s2a)) s2b"
        using inline.simps(5)[of Pr2 n l s2a s2b] \<open>s2 = s2a ; s2b\<close> by meson
      ultimately show "inline Pr1 n l ?s1 = inline Pr2 n l s2"
        by simp
    qed
    then show ?case by simp
next
  case (6 Pr1 n l a b)
  let ?s1 = "If a b"
  have "\<And>s2. same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2 \<Longrightarrow> inline Pr1 n l ?s1 = inline Pr2 n l s2"
  proof -
      fix s2 assume asm0: "same_not_annotated_programs Pr1 Pr2 \<and> same_not_annotated_stmt ?s1 s2"
      have "\<exists>s2a s2b. s2 = If s2a s2b"
      proof (rule ccontr)
        assume asm: "\<nexists>s2a s2b. s2 = If s2a s2b"
        then have "If a b \<noteq> s2" by auto
        then have "\<not> same_not_annotated_stmt (If a b) s2"
        proof (cases s2)
          case (If x61 x62)
          then show ?thesis using asm by blast
        qed (simp_all)
        then show "False" using asm0 by simp
      qed
      then obtain s2a s2b where "s2 = If s2a s2b" by blast
      then have "inline Pr1 n l a = inline Pr2 n l s2a" 
        using "6.hyps"(1) asm0 same_not_annotated_stmt.simps by blast
      moreover have "inline Pr1 n l b = inline Pr2 n l s2b"
        using "6.hyps"(2) \<open>s2 = If s2a s2b\<close> asm0 by auto
      ultimately show "inline Pr1 n l ?s1 = inline Pr2 n l s2"
        by (simp add: \<open>s2 = stmt.If s2a s2b\<close>)
    qed
    then show ?case by simp
  qed (auto)
  then show ?thesis using assms by simp
qed

theorem soundness:
  assumes "wf_program Pr"
      and "wf_stmt Pr s"
      and "SC Pr n {u} (modif s) s"
      and "ver_program Pr"
      and "ver Pr {u} s"
    shows "ver Pr {u} (inline Pr n (modif s) s)"
proof -
  have "SP Pr n {u} (modif s) s" 
    by (simp add: soundness_invariant)
  then have "(\<forall>\<phi>' \<phi>. \<phi>' \<in> {u} \<and> \<phi> << \<phi>' \<and> ver Pr {\<phi>} s \<longrightarrow> ver Pr {\<phi>'} (inline Pr n (modif s) s) \<and> sem Pr {\<phi>'} (inline Pr n (modif s) s) >> sem Pr {\<phi>} s)"
    using SP_def assms(1) assms(2) assms(3) assms(4) no_inter_def no_inter_single_def set_eq_subset store_empty by auto
  then show ?thesis using assms(5) by force
qed

end

end
