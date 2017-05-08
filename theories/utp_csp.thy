(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_csp.thy                                                          *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 31 Jan 2017 *)

section {* Theory of CSP *}

theory utp_csp
  imports utp_rea_designs
begin

subsection {* CSP Alphabet *}

alphabet '\<phi> csp_vars = "'\<sigma> rsp_vars" +
  ref :: "'\<phi> set"

text {*
  The following two locale interpretations are a technicality to improve the
  behaviour of the automatic tactics. They enable (re)interpretation of state
  spaces in order to remove any occurrences of lens types, replacing them by
  tuple types after the tactics @{method pred_simp} and @{method rel_simp}
  are applied. Eventually, it would be desirable to automate preform these
  interpretations automatically as part of the @{command alphabet} command.
*}

interpretation alphabet_csp_prd:
  lens_interp "\<lambda>(ok, wait, tr, m). (ok, wait, tr, ref\<^sub>v m, more m)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_csp_rel:
  lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', m, m').
    (ok, ok', wait, wait', tr, tr', ref\<^sub>v m, ref\<^sub>v m', more m, more m')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

type_synonym ('\<sigma>,'\<phi>) st_csp = "('\<sigma>, '\<phi> list, ('\<phi>, unit) csp_vars_scheme) rsp"
type_synonym ('\<sigma>,'\<phi>) action  = "('\<sigma>,'\<phi>) st_csp hrel"

translations
  (type) "('\<sigma>,'\<phi>) st_csp" <= (type) "('\<phi> list, ('\<sigma>, _ csp_vars) rsp_vars_ext) rp"

type_synonym '\<phi> csp = "(unit,'\<phi>) st_csp"
type_synonym '\<phi> rel_csp  = "'\<phi> csp hrel"

notation csp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>c")
notation csp_vars_child_lens ("\<Sigma>\<^sub>C")

subsection {* CSP Trace Merge *}

fun tr_par ::
  "'\<theta> set \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list set" where
"tr_par cs [] [] = {[]}" |
"tr_par cs (e # t) [] = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs t []))" |
"tr_par cs [] (e # t) = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs [] t))" |
"tr_par cs (e\<^sub>1 # t\<^sub>1) (e\<^sub>2 # t\<^sub>2) =
  (if e\<^sub>1 = e\<^sub>2
    then
      if e\<^sub>1 \<in> cs (* \<and> e\<^sub>2 \<in> cs *)
        then {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 t\<^sub>2)
        else
          ({[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))) \<union>
          ({[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))
    else
      if e\<^sub>1 \<in> cs then
        if e\<^sub>2 \<in> cs then {[]}
        else
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2)
      else
        if e\<^sub>2 \<in> cs then
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))
        else
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)) \<union>
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))"

subsubsection {* Lifted Trace Merge *}

syntax "_utr_par" ::
  "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(_ \<star>\<^bsub>_\<^esub>/ _)" [100, 0, 101] 100)

text {* The function @{const trop} is used to lift ternary operators. *}

translations
  "t1 \<star>\<^bsub>cs\<^esub> t2" == "(CONST trop) (CONST tr_par) cs t1 t2"

subsubsection {* Trace Merge Lemmas *}

lemma tr_par_empty:
"tr_par cs t1 [] = {takeWhile (\<lambda>x. x \<notin> cs) t1}"
"tr_par cs [] t2 = {takeWhile (\<lambda>x. x \<notin> cs) t2}"
-- {* Subgoal 1 *}
apply (induct t1; simp)
-- {* Subgoal 2 *}
apply (induct t2; simp)
done

lemma tr_par_sym:
"tr_par cs t1 t2 = tr_par cs t2 t1"
apply (induct t1 arbitrary: t2)
-- {* Subgoal 1 *}
apply (simp add: tr_par_empty)
-- {* Subgoal 2 *}
apply (induct_tac t2)
-- {* Subgoal 2.1 *}
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (clarsimp)
apply (blast)
done

subsection {* Healthiness Conditions *}

text {* We here define extra healthiness conditions for CSP processes. *}

abbreviation CSP1 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP1(P) \<equiv> RD1(P)"

abbreviation CSP2 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP2(P) \<equiv> RD2(P)"

abbreviation CSP :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP(P) \<equiv> SRD(P)"

definition STOP :: "'\<phi> rel_csp" where
[upred_defs]: "STOP = CSP1($ok\<acute> \<and> R3c($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition SKIP :: "'\<phi> rel_csp" where
[upred_defs]: "SKIP = \<^bold>R\<^sub>s(\<exists> $ref \<bullet> CSP1(II))"

definition Stop :: "('\<sigma>, '\<phi>) action" where
[upred_defs]: "Stop = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition Skip :: "('\<sigma>, '\<phi>) action" where
[upred_defs]: "Skip = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st))"

definition CSP3 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "CSP3(P) = (Skip ;; P)"

definition CSP4 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "CSP4(P) = (P ;; Skip)"

definition NCSP :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "NCSP = CSP3 \<circ> CSP4 \<circ> CSP"

subsection {* Healthiness condition properties *}

text {* @{term SKIP} is the same as @{term Skip}, and @{term STOP} is the same as @{term Stop},
  when we consider stateless CSP processes. This is because any reference to the @{term st}
  variable degenerates when the alphabet type coerces its type to be empty. We therefore
  need not consider @{term SKIP} and @{term STOP} actions. *}

theorem SKIP_is_Skip: "SKIP = Skip"
  by (rel_auto)

theorem STOP_is_Stop: "STOP = Stop"
  by (rel_simp, meson minus_zero_eq order_refl ordered_cancel_monoid_diff_class.diff_cancel)

lemma Skip_is_CSP [closure]:
  "Skip is CSP"
  by (simp add: Skip_def RHS_design_is_SRD unrest)

lemma Skip_RHS_tri_design: "Skip = \<^bold>R\<^sub>s(true \<turnstile> (false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)))"
  by (rel_auto)

lemma Stop_is_CSP [closure]:
  "Stop is CSP"
  by (simp add: Stop_def RHS_design_is_SRD unrest)
    
lemma Stop_RHS_tri_design: "Stop = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr) \<diamondop> false)"
  by (rel_auto)
    
lemma pre_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P)"
  by (simp add: pre\<^sub>R_def unrest)

lemma peri_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> peri\<^sub>R(P)"
  by (simp add: peri\<^sub>R_def unrest)

lemma post_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> post\<^sub>R(P)"
  by (simp add: post\<^sub>R_def unrest)

lemma cmt_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> cmt\<^sub>R(P)"
  by (simp add: cmt\<^sub>R_def unrest)

lemma RHS_design_ref_unrest [unrest]:
  "\<lbrakk>$ref \<sharp> P; $ref \<sharp> Q \<rbrakk> \<Longrightarrow> $ref \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q))\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma Skip_left_lemma:
  assumes "P is CSP"
  shows "Skip ;; P = \<^bold>R\<^sub>s ((\<not> (\<exists> $ref \<bullet> (\<not> pre\<^sub>R P))) \<turnstile> (\<exists> $ref \<bullet> cmt\<^sub>R P))"
proof -
  have "Skip ;; P = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    using assms by (simp add: Skip_def SRD_reactive_design_alt)
  also have "... = \<^bold>R\<^sub>s ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st) \<and> \<not> $wait\<acute>) ;; (\<not> pre\<^sub>R P)) \<turnstile>
                      (($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> cmt\<^sub>R P))"
    by (simp add: RHS_design_composition unrest R2s_true R1_false R2s_conj R2s_not R2s_wait' R1_extend_conj R1_R2s_tr'_eq_tr R1_neg_R2s_pre_RHS assms R1_R2s_cmt_SRD R2s_st'_eq_st)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<exists> $ref \<bullet> (\<not> pre\<^sub>R P))) \<turnstile>
                      (($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<exists> $ref \<bullet> (\<not> pre\<^sub>R P))) \<turnstile> (\<exists> $ref \<bullet> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma Skip_left_unit:
  assumes "P is CSP" "$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
  shows "Skip ;; P = P"
    using assms
    by (simp add: Skip_left_lemma)
       (metis SRD_reactive_design_alt cmt_unrest_ref cmt_wait_false ex_unrest pre_unrest_ref pre_wait_false unrest_not utp_pred.double_compl)

lemma CSP3_intro:
  "\<lbrakk> P is CSP; $ref \<sharp> P\<lbrakk>false/$wait\<rbrakk> \<rbrakk> \<Longrightarrow> P is CSP3"
  by (simp add: CSP3_def Healthy_def' Skip_left_unit)

lemma ref_unrest_RHS_design:
  assumes "$ref \<sharp> P" "$ref \<sharp> Q\<^sub>1" "$ref \<sharp> Q\<^sub>2"
  shows "$ref \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<^sub>f"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def unrest usubst assms)
    
lemma CSP3_SRD_intro:
  assumes "P is CSP" "$ref \<sharp> pre\<^sub>R(P)" "$ref \<sharp> peri\<^sub>R(P)" "$ref \<sharp> post\<^sub>R(P)"
  shows "P is CSP3"
proof -
  have P: "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
    by (simp add: SRD_reactive_design_alt assms(1) wait'_cond_peri_post_cmt[THEN sym])
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) is CSP3"
    by (rule CSP3_intro, simp add: assms P, simp add: ref_unrest_RHS_design assms)
  thus ?thesis
    by (simp add: P)
qed
   
lemma Skip_unrest_ref [unrest]: "$ref \<sharp> Skip\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: Skip_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma Skip_unrest_ref' [unrest]: "$ref\<acute> \<sharp> Skip\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: Skip_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma CSP3_iff:
  assumes "P is CSP"
  shows "P is CSP3 \<longleftrightarrow> ($ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>)"
proof
  assume 1: "P is CSP3"
  have "$ref \<sharp> (Skip ;; P)\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: usubst unrest)
  with 1 show "$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
    by (metis CSP3_def Healthy_def)
next
  assume 1:"$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
  show "P is CSP3"
    by (simp add: 1 CSP3_intro assms)
qed
  
lemma CSP3_unrest_ref [unrest]:
  assumes "P is CSP" "P is CSP3"
  shows "$ref \<sharp> pre\<^sub>R(P)" "$ref \<sharp> peri\<^sub>R(P)" "$ref \<sharp> post\<^sub>R(P)"
proof -
  have a:"($ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>)"
    using CSP3_iff assms by blast
  from a show "$ref \<sharp> pre\<^sub>R(P)"
    by (rel_auto)
  from a show "$ref \<sharp> peri\<^sub>R(P)"      
    by (rel_auto)
  from a show "$ref \<sharp> post\<^sub>R(P)"      
    by (rel_auto)      
qed
      
lemma CSP3_Skip [closure]:
  "Skip is CSP3"
  by (rule CSP3_intro, simp add: Skip_is_CSP, simp add: Skip_def unrest)

lemma CSP3_Stop [closure]:
  "Stop is CSP3"
  by (rule CSP3_intro, simp add: Stop_is_CSP, simp add: Stop_def unrest)

lemma CSP3_Idempotent [closure]: "Idempotent CSP3"
  by (metis (no_types, lifting) CSP3_Skip CSP3_def Healthy_if Idempotent_def seqr_assoc)

lemma CSP3_Continuous: "Continuous CSP3"
  by (simp add: Continuous_def CSP3_def seq_Sup_distl)

lemma Skip_right_lemma:
  assumes "P is CSP"
  shows "P ;; Skip = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
proof -
  have "P ;; Skip = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) ;; \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st))"
    using assms by (simp add: Skip_def SRD_reactive_design_alt)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile>
                       (cmt\<^sub>R P ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st)))"
    by (simp add: RHS_design_composition unrest R2s_true R1_false R2s_conj R2s_not R2s_wait' R1_extend_conj R1_R2s_tr'_eq_tr R1_neg_R2s_pre_RHS assms R1_R2s_cmt_SRD R2s_st'_eq_st)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile>
                       ((cmt\<^sub>R P ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)) \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P ;; ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait \<and> $st\<acute> =\<^sub>u $st))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P ;; ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait \<and> $st\<acute> =\<^sub>u $st))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma Skip_right_tri_lemma:
  assumes "P is CSP"
  shows "P ;; Skip = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R P)))"
proof -
  have "((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)) = ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R P))"
    by (rel_auto)
  thus ?thesis by (simp add: Skip_right_lemma[OF assms])
qed

lemma CSP4_intro:
  assumes "P is CSP" "(\<not> pre\<^sub>R(P)) ;; R1(true) = (\<not> pre\<^sub>R(P))"
          "$st\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk>" "$ref\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>"
  shows "P is CSP4"
proof -
  have "CSP4(P) = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (simp add: CSP4_def Skip_right_lemma assms(1))
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (simp add: assms(2) cond_var_subst_left cond_var_subst_right)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> ((\<exists> $st\<acute> \<bullet> (cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk>) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>)))"
    by (simp add: usubst unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> ((cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (simp add: ex_unrest assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
    by (simp add: cond_var_split)
  also have "... = P"
    by (simp add: SRD_reactive_design_alt assms(1))
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma Skip_srdes_right_unit:
  "(Skip :: ('\<sigma>,'\<phi>) action) ;; II\<^sub>R = Skip"
proof -
  have "($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) ;; ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R)
         = (($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) :: ('\<sigma>,'\<phi>) action)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Skip_RHS_tri_design srdes_skip_tri_design RHS_tri_normal_design_composition
                  unrest R2c_true Healthy_def R1_false R2c_false R1_extend_conj R1_tr'_eq_tr R2c_and
                  R2c_tr'_minus_tr R2c_st'_eq_st wp R2c_lift_rea)
qed

lemma Skip_srdes_left_unit:
  "II\<^sub>R ;; (Skip :: ('\<sigma>,'\<phi>) action) = Skip"
proof -
  have "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R) ;; ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)
         = (($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) :: ('\<sigma>,'\<phi>) action)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Skip_RHS_tri_design srdes_skip_tri_design RHS_tri_normal_design_composition
                  unrest R2c_true Healthy_def R1_false R2c_false R1_extend_conj R1_tr'_eq_tr R2c_and
                  R2c_tr'_minus_tr R2c_st'_eq_st wp R2c_lift_rea)
qed

lemma CSP4_right_subsumes_RD3: "RD3(CSP4(P)) = CSP4(P)"
  by (metis (no_types, hide_lams) CSP4_def RD3_def Skip_srdes_right_unit seqr_assoc)

lemma CSP4_implies_RD3: "P is CSP4 \<Longrightarrow> P is RD3"
  by (metis CSP4_right_subsumes_RD3 Healthy_def)

lemma CSP4_tri_intro:
  assumes "P is CSP" "(\<not> pre\<^sub>R(P)) ;; R1(true) = (\<not> pre\<^sub>R(P))" "$st\<acute> \<sharp> peri\<^sub>R(P)" "$ref\<acute> \<sharp> post\<^sub>R(P)"
  shows "P is CSP4"
  using assms
  by (rule_tac CSP4_intro, simp_all add: pre\<^sub>R_def peri\<^sub>R_def post\<^sub>R_def usubst cmt\<^sub>R_def)

lemma CSP3_commutes_CSP4: "CSP3(CSP4(P)) = CSP4(CSP3(P))"
  by (simp add: CSP3_def CSP4_def seqr_assoc)

lemma NCSP_implies_CSP [closure]: "P is NCSP \<Longrightarrow> P is CSP"
  by (metis (no_types, hide_lams) CSP3_def CSP4_def Healthy_def NCSP_def SRD_idem SRD_seqr_closure Skip_is_CSP comp_apply)
    
lemma NCSP_implies_CSP3 [closure]:
  "P is NCSP \<Longrightarrow> P is CSP3"
  by (metis (no_types, lifting) CSP3_def Healthy_def' NCSP_def Skip_is_CSP Skip_left_unit Skip_unrest_ref comp_apply seqr_assoc)

lemma NCSP_implies_CSP4 [closure]:
  "P is NCSP \<Longrightarrow> P is CSP4"
  by (metis (no_types, hide_lams) CSP3_commutes_CSP4 Healthy_def NCSP_def NCSP_implies_CSP NCSP_implies_CSP3 comp_apply)
    
lemma NCSP_implies_RD3 [closure]: "P is NCSP \<Longrightarrow> P is RD3"
  by (metis CSP3_commutes_CSP4 CSP4_right_subsumes_RD3 Healthy_def NCSP_def comp_apply)

lemma NCSP_implies_NSRD [closure]: "P is NCSP \<Longrightarrow> P is NSRD"
  by (simp add: NCSP_implies_CSP NCSP_implies_RD3 SRD_RD3_implies_NSRD)

lemma NCSP_subset_implies_CSP [closure]: 
  "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<Longrightarrow> A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using NCSP_implies_CSP by blast

lemma NCSP_subset_implies_NSRD [closure]: 
  "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<Longrightarrow> A \<subseteq> \<lbrakk>NSRD\<rbrakk>\<^sub>H"
  using NCSP_implies_NSRD by blast
    
lemma CSP_Healthy_subset_member [closure]: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP"
  by (simp add: is_Healthy_subset_member)

lemma CSP3_Healthy_subset_member [closure]: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP3"
  by (simp add: is_Healthy_subset_member)

lemma CSP4_Healthy_subset_member [closure]: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP4"
  by (simp add: is_Healthy_subset_member)
    
lemma NCSP_Healthy_subset_member [closure]: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is NCSP"
  by (simp add: is_Healthy_subset_member)
    
lemma NCSP_intro:
  assumes "P is CSP" "P is CSP3" "P is CSP4"
  shows "P is NCSP"
  by (metis Healthy_def NCSP_def assms comp_eq_dest_lhs)
    
lemma CSP4_neg_pre_unit:
  assumes "P is CSP" "P is CSP4"
  shows "(\<not> pre\<^sub>R(P)) ;; R1(true) = (\<not> pre\<^sub>R(P))"
  by (simp add: CSP4_implies_RD3 NSRD_neg_pre_unit SRD_RD3_implies_NSRD assms(1) assms(2))

lemma NSRD_CSP4_intro:
  assumes "P is CSP" "P is CSP4"
  shows "P is NSRD"
  by (simp add: CSP4_implies_RD3 SRD_RD3_implies_NSRD assms(1) assms(2))
    
lemma CSP4_st'_unrest_peri:
  assumes "P is CSP" "P is CSP4"
  shows "$st\<acute> \<sharp> peri\<^sub>R(P)"
  by (simp add: NSRD_CSP4_intro NSRD_st'_unrest_peri assms)

lemma CSP4_healthy_form:
  assumes "P is CSP" "P is CSP4"
  shows "P = \<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P))))"
proof -
  have "P = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (metis CSP4_def Healthy_def Skip_right_lemma assms(1) assms(2))
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (metis (no_types, hide_lams) subst_wait'_left_subst subst_wait'_right_subst wait'_cond_def)
  also have "... = \<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P))))"
    by (simp add: wait'_cond_def usubst peri\<^sub>R_def post\<^sub>R_def cmt\<^sub>R_def unrest)
  finally show ?thesis .
qed

lemma CSP4_ref'_unrest_pre:
  assumes "P is CSP" "P is CSP4"
  shows "$ref\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(P) = pre\<^sub>R(\<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P)))))"
    using CSP4_healthy_form assms(1) assms(2) by fastforce
  also have "... = (\<not> R1 (R2c ((\<not> pre\<^sub>R P) ;; R1 true)))"
    by (simp add: rea_pre_RHS_design usubst unrest)
  also have "$ref\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def unrest)
  finally show ?thesis .
qed

lemma CSP4_ref'_unrest_post:
  assumes "P is CSP" "P is CSP4"
  shows "$ref\<acute> \<sharp> post\<^sub>R(P)"
proof -
  have "post\<^sub>R(P) = post\<^sub>R(\<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P)))))"
    using CSP4_healthy_form assms(1) assms(2) by fastforce
  also have "... = R1 (R2c (\<not> (\<not> pre\<^sub>R P) ;; R1 true \<Rightarrow> (\<exists> $ref\<acute> \<bullet> post\<^sub>R P)))"
    by (simp add: rea_post_RHS_design usubst unrest)
  also have "$ref\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def unrest)
  finally show ?thesis .
qed
  
lemma CSP3_Chaos [closure]: "Chaos is CSP3"
  by (simp add: Chaos_def, rule CSP3_intro, simp_all add: RHS_design_is_SRD unrest)

lemma CSP4_Chaos [closure]: "Chaos is CSP4"
  by (rule CSP4_tri_intro, simp_all add: closure rdes unrest, rel_auto) 

lemma CSP3_Miracle [closure]: "Miracle is CSP3"
  by (simp add: Miracle_def, rule CSP3_intro, simp_all add: RHS_design_is_SRD unrest)

lemma CSP4_Miracle [closure]: "Miracle is CSP4"
  by (rule CSP4_tri_intro, simp_all add: closure rdes unrest) 

lemma NCSP_seqr_closure [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P ;; Q is NCSP"
  by (metis (no_types, lifting) CSP3_def CSP4_def Healthy_def' NCSP_implies_CSP NCSP_implies_CSP3 
      NCSP_implies_CSP4 NCSP_intro SRD_seqr_closure assms(1) assms(2) seqr_assoc)
    
lemma R1_ref_unrest [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref_unrest [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R1_ref'_unrest [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref'_unrest [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R2s_notin_ref': "R2s(\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) = (\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (pred_auto)
    
lemma CSP4_Skip [closure]: "Skip is CSP4"
  apply (rule CSP4_intro, simp_all add: Skip_is_CSP)
  apply (simp_all add: Skip_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest R2c_false R1_false)
done

lemma NCSP_Skip [closure]: "Skip is NCSP"
  by (metis CSP3_Skip CSP4_Skip Healthy_def NCSP_def Skip_is_CSP comp_apply)
  
lemma CSP4_Stop [closure]: "Stop is CSP4"
  apply (rule CSP4_intro, simp_all add: Stop_is_CSP)
  apply (simp_all add: Stop_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest R2c_false R1_false)
done

lemma NCSP_Stop [closure]: "Stop is NCSP"
  by (metis CSP3_Stop CSP4_Stop Healthy_def NCSP_def Stop_is_CSP comp_apply)
  
lemma CSP4_Idempotent: "Idempotent CSP4"
  by (metis (no_types, lifting) CSP3_Skip CSP3_def CSP4_def Healthy_if Idempotent_def seqr_assoc)

lemma CSP4_Continuous: "Continuous CSP4"
  by (simp add: Continuous_def CSP4_def seq_Sup_distr)

lemma preR_Stop [rdes]: "pre\<^sub>R(Stop) = true"
  by (simp add: Stop_def Stop_is_CSP rea_pre_RHS_design unrest usubst R2c_false R1_false)
    
lemma periR_Stop [rdes]: "peri\<^sub>R(Stop) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_auto) using minus_zero_eq by blast 

lemma postR_Stop [rdes]: "post\<^sub>R(Stop) = false"
  by (rel_auto)
    
lemma cmtR_Stop [rdes]: "cmt\<^sub>R(Stop) = ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)"
  apply (rel_auto) using minus_zero_eq by blast

lemma preR_Skip [rdes]: "pre\<^sub>R(Skip) = true"
  by (rel_auto)
    
lemma periR_Skip [rdes]: "peri\<^sub>R(Skip) = false"
  by (rel_auto)
    
lemma postR_Skip [rdes]: "post\<^sub>R(Skip) = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"
  apply (rel_auto) using minus_zero_eq by blast
    
lemma NCSP_Idempotent [closure]: "Idempotent NCSP"
  by (clarsimp simp add: NCSP_def Idempotent_def)
     (metis (no_types, hide_lams) CSP3_Idempotent CSP3_def CSP4_Idempotent CSP4_def Healthy_def Idempotent_def SRD_idem SRD_seqr_closure Skip_is_CSP seqr_assoc)

lemma NCSP_Continuous [closure]: "Continuous NCSP"
  by (simp add: CSP3_Continuous CSP4_Continuous Continuous_comp NCSP_def SRD_Continuous)

subsection {* CSP theories *}
  
typedecl TCSP

abbreviation "TCSP \<equiv> UTHY(TCSP, ('\<sigma>,'\<phi>) st_csp)"

overloading
  tcsp_hcond   == "utp_hcond :: (TCSP, ('\<sigma>,'\<phi>) st_csp) uthy \<Rightarrow> (('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) health"
begin
  definition tcsp_hcond :: "(TCSP, ('\<sigma>,'\<phi>) st_csp) uthy \<Rightarrow> (('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) health" where
  [upred_defs]: "tcsp_hcond T = NCSP"
end
     
interpretation csp_theory: utp_theory_continuous "UTHY(TCSP, ('\<sigma>,'\<phi>) st_csp)"
  rewrites "\<And> P. P \<in> carrier (uthy_order TCSP) \<longleftrightarrow> P is NCSP"
  and "P is \<H>\<^bsub>TCSP\<^esub> \<longleftrightarrow> P is NCSP"
  and "carrier (uthy_order TCSP) \<rightarrow> carrier (uthy_order TCSP) \<equiv> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  and "le (uthy_order TCSP) = op \<sqsubseteq>"
  by (unfold_locales, simp_all add: tcsp_hcond_def NCSP_Continuous Healthy_Idempotent Healthy_if NCSP_Idempotent)
   
declare csp_theory.top_healthy [simp del]
declare csp_theory.bottom_healthy [simp del]

    
lemma csp_bottom_Chaos: "\<^bold>\<bottom>\<^bsub>TCSP\<^esub> = Chaos"
proof -
  have 1: "\<^bold>\<bottom>\<^bsub>TCSP\<^esub> = CSP3 (CSP4 (CSP true))"
    by (simp add: csp_theory.healthy_bottom, simp add: tcsp_hcond_def NCSP_def)
  also have 2:"... = CSP3 (CSP4 Chaos)"
    by (metis srdes_hcond_def srdes_theory_continuous.healthy_bottom)
  also have 3:"... = Chaos"
    by (metis CSP3_Chaos CSP4_Chaos Healthy_def')
  finally show ?thesis .
qed
    
subsection {* CSP Constructs *}

translations
  (type) "('\<sigma>, '\<phi>) st_csp" <= (type) "(_ list, ('\<sigma>, (_, '\<phi>) csp_vars) rsp_vars_ext) rp"

definition AssignsCSP :: "'\<sigma> usubst \<Rightarrow> ('\<sigma>, '\<phi>) action" ("\<langle>_\<rangle>\<^sub>C") where
[upred_defs]: "AssignsCSP \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S))"

syntax
  "_assigns_csp" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>C" 90)

translations
  "_assigns_csp xs vs" => "CONST AssignsCSP (_mk_usubst (CONST id) xs vs)"
  "x :=\<^sub>C v" <= "CONST AssignsCSP (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x :=\<^sub>C v" <= "CONST AssignsCSP (CONST subst_upd (CONST id) x v)"
  "x,y :=\<^sub>C u,v" <= "CONST AssignsCSP (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

definition Guard ::
  "'\<sigma> cond \<Rightarrow>
   ('\<sigma>, '\<phi>) action \<Rightarrow>
   ('\<sigma>, '\<phi>) action" (infixr "&\<^sub>u" 70) where
[upred_defs]: "g &\<^sub>u A = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R(A)) \<turnstile> ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R(A)) \<or> (\<not> \<lceil>g\<rceil>\<^sub>S\<^sub><) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition ExtChoice ::
  "('\<sigma>, '\<phi>) action set \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "ExtChoice A = \<^bold>R\<^sub>s((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P)) \<turnstile> ((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R(P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R(P))))"

syntax
  "_ExtChoice" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<box>_\<in>_ \<bullet>/ _)" [0, 0, 10] 10)

translations
  "\<box>P\<in>A \<bullet> B"   \<rightleftharpoons> "CONST ExtChoice ((\<lambda>P. B) ` A)"

definition extChoice ::
  "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\<box>" 65) where
[upred_defs]: "P \<box> Q \<equiv> ExtChoice {P, Q}"

definition do\<^sub>u ::
  "('\<phi>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "do\<^sub>u e = (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>e\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>e\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st))"

definition DoCSP :: "('\<phi>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" ("do\<^sub>C") where
[upred_defs]: "DoCSP a = \<^bold>R\<^sub>s(true \<turnstile> do\<^sub>u a)"

definition PrefixCSP ::
  "('\<phi>, '\<sigma>) uexpr \<Rightarrow>
  ('\<sigma>, '\<phi>) action \<Rightarrow>
  ('\<sigma>, '\<phi>) action" ("_ \<^bold>\<rightarrow> _" [81, 80] 80) where
[upred_defs]: "PrefixCSP a P = (do\<^sub>C(a) ;; CSP(P))"

abbreviation "OutputCSP c v P \<equiv> PrefixCSP (c\<cdot>v)\<^sub>u P"

abbreviation GuardedChoiceCSP :: "'\<theta> set \<Rightarrow> ('\<theta> \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow> ('\<sigma>, '\<theta>) action" where
"GuardedChoiceCSP A P \<equiv> (\<box> x\<in>A \<bullet> \<guillemotleft>x\<guillemotright> \<^bold>\<rightarrow> P(x))"

syntax
  "_GuardedChoiceCSP" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box> _ \<in> _ \<^bold>\<rightarrow> _" [0,0,85] 86)

translations
  "\<box> x\<in>A \<^bold>\<rightarrow> P" == "CONST GuardedChoiceCSP A (\<lambda> x. P)"

text {* This version of input prefix is implemented using iterated external choice and so does not
  depend on the existence of local variables. *}

definition InputCSP ::
  "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> upred) \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow> ('\<sigma>, '\<theta>) action" where
[upred_defs]: "InputCSP c A P = (\<box> x\<in>UNIV \<bullet> A(x) &\<^sub>u PrefixCSP (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u (P x))"

definition InputVarCSP :: "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> upred) \<Rightarrow> ('a \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" where
"InputVarCSP c A x P = InputCSP c A (\<lambda> v. \<langle>[x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>]\<rangle>\<^sub>C) ;; CSP(P)"

definition do\<^sub>I :: "
  ('a, '\<theta>) chan \<Rightarrow>
  _ \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow>
  ('\<sigma>, '\<theta>) action" where
"do\<^sub>I c x P = (
  ($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>$x\<acute>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>)))"

subsection {* Syntax and Translations for Prefix *}

text {* We next configure a syntax for mixed prefixes. *}

nonterminal prefix_elem and mixed_prefix

syntax "_end_prefix" :: "prefix_elem \<Rightarrow> mixed_prefix" ("_")
  
text {* Input Prefix: @{text "\<dots>?(x)"} *}

syntax "_simple_input_prefix" :: "id \<Rightarrow> prefix_elem"  ("?'(_')")
  
text {* Input Prefix with Constraint: @{text "\<dots>?(x : P)"} *}

syntax "_input_prefix" :: "id \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> prefix_elem" ("?'(_ :/ _')")

text {* Output Prefix: @{text "\<dots>![v]e"} *}

text {* A variable name must currently be provided for outputs, too. Fix?! *}

syntax "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem" ("!'(_')" [999] 999)
syntax "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem" (".'(_')" [999] 999)

syntax (output) "_output_prefix_pp" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem" ("!'(_')")

syntax
  "_prefix_aux" :: "pttrn \<Rightarrow> logic \<Rightarrow> prefix_elem"
  
text {* Mixed-Prefix Action: @{text "c\<dots>(prefix) \<^bold>\<rightarrow> A"} *}

syntax "_mixed_prefix" :: "prefix_elem \<Rightarrow> mixed_prefix \<Rightarrow> mixed_prefix" ("__")

syntax 
  "_prefix_action" ::
  "('a, '\<epsilon>) chan \<Rightarrow> mixed_prefix \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> ('\<sigma>, '\<epsilon>) action"
  ("(__ \<^bold>\<rightarrow>/ _)" [81, 81, 80] 80)
  
text {* Syntax translations *}

abbreviation lconj :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('b \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<times> 'b \<Rightarrow> '\<alpha> upred)" (infixr "\<and>\<^sub>l" 35)
where "(P \<and>\<^sub>l Q) \<equiv> (\<lambda> (x,y). P x \<and> Q y)"
 
definition [upred_defs]: "outp_constraint v \<equiv> (\<lambda> x. \<guillemotleft>x\<guillemotright> =\<^sub>u v)"
  
translations
  "_simple_input_prefix x" \<rightleftharpoons> "_input_prefix x true"
  "_mixed_prefix (_input_prefix x P) (_prefix_aux y Q)" \<rightharpoonup>
  "_prefix_aux (_pattern x y) ((\<lambda> x. P) \<and>\<^sub>l Q)"
  "_mixed_prefix (_output_prefix P) (_prefix_aux y Q)" \<rightharpoonup>
  "_prefix_aux (_pattern _idtdummy y) ((CONST outp_constraint P) \<and>\<^sub>l Q)"
  "_end_prefix (_input_prefix x P)" \<rightharpoonup> "_prefix_aux x (\<lambda> x. P)"
  "_end_prefix (_output_prefix P)" \<rightharpoonup> "_prefix_aux _idtdummy (CONST outp_constraint P)"
  "_prefix_action c (_prefix_aux x P) A" == "(CONST InputCSP) c P (\<lambda>x. A)"
  
text {* Basic print translations; more work needed *}
  
translations
  "_input_prefix x P" <= "_prefix_aux v (\<lambda>x. P)"
  "_simple_input_prefix x" <= "_input_prefix x true"
  "_output_prefix v" <= "_prefix_aux p (CONST outp_constraint v)"  
  "x!(v) \<^bold>\<rightarrow> P" <= "CONST OutputCSP x v P"
  
term "x?(v) \<^bold>\<rightarrow> P"
term "x?(v:false) \<^bold>\<rightarrow> P"
term "x!(\<langle>1\<rangle>) \<^bold>\<rightarrow> P"
term "x?(v)!(1) \<^bold>\<rightarrow> P"
term "x!(\<langle>1\<rangle>)!(2)?(v:true) \<^bold>\<rightarrow> P"
  
text {* Basic translations for state variable communications *}
  
syntax
  "_csp_input_var"  :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?$_:_ \<^bold>\<rightarrow> _" [81, 0, 0, 80] 80)
  "_csp_inputu_var" :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?$_ \<^bold>\<rightarrow> _" [81, 0, 80] 80)

translations
  "c\<^bold>?$x:A \<^bold>\<rightarrow> P" \<rightleftharpoons> "CONST InputVarCSP c x A P"
  "c\<^bold>?$x \<^bold>\<rightarrow> P"   \<rightharpoonup> "CONST InputVarCSP c x (CONST UNIV) P"
  "c\<^bold>?$x \<^bold>\<rightarrow> P"   <= "c\<^bold>?$x:true \<^bold>\<rightarrow> P"  
  
subsection {* Closure properties *}

lemma CSP3_Sup_closure [closure]:
  "A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> A) is CSP3"
  apply (auto simp add: CSP3_def Healthy_def seq_Sup_distl)
  apply (rule cong[of Sup])
  apply (simp)
  using image_iff apply force
done

lemma CSP4_Sup_closure [closure]:
  "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> A) is CSP4"
  apply (auto simp add: CSP4_def Healthy_def seq_Sup_distr)
  apply (rule cong[of Sup])
  apply (simp)
  using image_iff apply force
done
  
lemma NCSP_Sup_closure [closure]: "\<lbrakk> A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> A) is NCSP"
  apply (rule NCSP_intro, simp_all add: closure)
  apply (metis (no_types, lifting) Ball_Collect CSP3_Sup_closure NCSP_implies_CSP3)
  apply (metis (no_types, lifting) Ball_Collect CSP4_Sup_closure NCSP_implies_CSP4)
done

lemma NCSP_SUP_closure [closure]: "\<lbrakk> \<And> i. P(i) is NCSP; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> i\<in>A. P(i)) is NCSP"
  by (metis (mono_tags, lifting) Ball_Collect NCSP_Sup_closure image_iff image_is_empty)
  
lemma AssignsCSP_CSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP"
  by (simp add: AssignsCSP_def RHS_tri_design_is_SRD unrest)

lemma AssignsCSP_CSP3 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP3"
  by (rule CSP3_intro, simp add: closure, rel_auto)

lemma AssignsCSP_CSP4 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP4"
  by (rule CSP4_intro, simp add: closure, rel_auto+)
    
lemma AssignsCSP_NCSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is NCSP"
  by (simp add: AssignsCSP_CSP AssignsCSP_CSP3 AssignsCSP_CSP4 NCSP_intro)    
  
lemma preR_AssignsCSP [rdes]: "pre\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = true"
  by (rel_auto)
    
lemma periR_AssignsCSP [rdes]: "peri\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = false"
  by (rel_auto)
    
lemma postR_AssignsCSP [rdes]: "post\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)"
  apply (rel_auto) using minus_zero_eq by auto

lemma R2c_tr_ext: "R2c ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>)"
  apply (rel_auto)
  apply (metis append_Nil diff_add_cancel_left' plus_list_def zero_list_def)
  apply (simp add: zero_list_def)
done
  
lemma R1_DoAct: "R1(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (rel_auto)
  
lemma R2c_DoAct: "R2c(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (rel_auto, simp_all add: zero_list_def minus_zero_eq, (metis less_eq_list_def prefix_concat_minus)+)
        
lemma DoCSP_alt_def: "do\<^sub>C(a) = R3h(CSP1($ok\<acute> \<and> do\<^sub>u(a)))"
  apply (simp add: DoCSP_def RHS_def design_def impl_alt_def  R1_R3h_commute R2c_R3h_commute R2c_disj
                   R2c_not R2c_ok R2c_ok' R2c_and R2c_DoAct R1_disj R1_extend_conj' R1_DoAct)
  apply (rel_auto)
done
  
lemma DoAct_unrests [unrest]:
  "$ok \<sharp> do\<^sub>u(a)" "$wait \<sharp> do\<^sub>u(a)"
  by (pred_auto)+
  
lemma DoCSP_RHS_tri:
  "do\<^sub>C(a) = \<^bold>R\<^sub>s(true \<turnstile> (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<diamondop> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st)))"
  by (simp add: DoCSP_def do\<^sub>u_def wait'_cond_def)

lemma CSP_DoCSP [closure]: "do\<^sub>C(a) is CSP"
  by (simp add: DoCSP_def do\<^sub>u_def RHS_design_is_SRD unrest)

lemma preR_DoCSP [rdes]: "pre\<^sub>R(do\<^sub>C(a)) = true"
  by (simp add: DoCSP_def rea_pre_RHS_design unrest usubst R2c_false R1_false)

lemma periR_DoCSP [rdes]: "peri\<^sub>R(do\<^sub>C(a)) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  apply (rel_auto) using minus_zero_eq by blast

lemma postR_DoCSP [rdes]: "post\<^sub>R(do\<^sub>C(a)) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st)"
  apply (rel_auto)
  using Prefix_Order.prefixE zero_list_def apply fastforce
  apply (simp add: zero_list_def)
done

lemma CSP3_DoCSP [closure]: "do\<^sub>C(a) is CSP3"
  by (rule CSP3_intro[OF CSP_DoCSP])
     (simp add: DoCSP_def do\<^sub>u_def RHS_def design_def R1_def R2c_def R2s_def R3h_def unrest usubst)

lemma CSP4_DoCSP [closure]: "do\<^sub>C(a) is CSP4"
  by (rule CSP4_tri_intro[OF CSP_DoCSP], simp_all add: preR_DoCSP periR_DoCSP postR_DoCSP unrest)
    
lemma NCSP_DoCSP [closure]: "do\<^sub>C(a) is NCSP"
  by (metis CSP3_DoCSP CSP4_DoCSP CSP_DoCSP Healthy_def NCSP_def comp_apply)
    
lemma CSP_PrefixCSP [closure]: "a \<^bold>\<rightarrow> P is CSP"
  by (simp add: CSP_DoCSP PrefixCSP_def closure)

lemma CSP3_PrefixCSP [closure]:
  "a \<^bold>\<rightarrow> P is CSP3"
  by (metis (no_types, hide_lams) CSP3_DoCSP CSP3_def Healthy_def PrefixCSP_def seqr_assoc)
    
lemma CSP4_PrefixCSP [closure]: 
  assumes "P is CSP" "P is CSP4"
  shows "a \<^bold>\<rightarrow> P is CSP4"
  by (metis (no_types, hide_lams) CSP4_def Healthy_def PrefixCSP_def assms(1) assms(2) seqr_assoc)
    
lemma NCSP_PrefixCSP [closure]:
  assumes "P is NCSP"
  shows "a \<^bold>\<rightarrow> P is NCSP"
  by (metis (no_types, hide_lams) CSP3_PrefixCSP CSP3_commutes_CSP4 CSP4_Idempotent CSP4_PrefixCSP 
            CSP_PrefixCSP Healthy_Idempotent Healthy_def NCSP_def NCSP_implies_CSP assms comp_apply)
    
lemma PrefixCSP_type [closure]: "PrefixCSP a \<in> \<lbrakk>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using CSP_PrefixCSP by blast

lemma PrefixCSP_Continuous [closure]: "Continuous (PrefixCSP a)"
   by (simp add: Continuous_def PrefixCSP_def ContinuousD[OF SRD_Continuous] seq_Sup_distl)
                    
lemma Guard_tri_design:
  "g &\<^sub>u P = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P) \<turnstile> (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P)))"
proof -
  have "(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R P \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) = (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P))"
    by (rel_auto, (metis (full_types))+)
  thus ?thesis by (simp add: Guard_def)
qed
  
lemma CSP_Guard [closure]: "b &\<^sub>u P is CSP"
  by (simp add: Guard_def, rule RHS_design_is_SRD, simp_all add: unrest)

lemma preR_Guard [rdes]: "P is CSP \<Longrightarrow> pre\<^sub>R(b &\<^sub>u P) = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P)"
  apply (simp add: Guard_tri_design rea_pre_RHS_design usubst unrest R2c_not R2c_impl R2c_preR R2c_lift_state_pre)
  apply (rel_blast)
done

lemma periR_Guard [rdes]:
  "\<lbrakk> P is CSP; $wait\<acute> \<sharp> pre\<^sub>R(P) \<rbrakk> \<Longrightarrow> peri\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P) \<Rightarrow> (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)))"
  apply (simp add: Guard_tri_design rea_peri_RHS_design usubst unrest R2c_not R2c_impl R2c_preR R2c_periR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr)
  apply (rel_blast)
done

lemma postR_Guard [rdes]:
  "\<lbrakk> P is CSP; $wait\<acute> \<sharp> pre\<^sub>R(P) \<rbrakk> \<Longrightarrow> post\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P) \<Rightarrow> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P))"
  apply (simp add: Guard_tri_design rea_post_RHS_design usubst unrest R2c_not R2c_and R2c_impl
                   R2c_preR R2c_postR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr)
  apply (rel_blast)
done

lemma CSP3_Guard [closure]:
  assumes "P is CSP" "P is CSP3"
  shows "b &\<^sub>u P is CSP3"
proof -
  from assms have 1:"$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: CSP_Guard CSP3_iff)
  hence "$ref \<sharp> pre\<^sub>R (P\<lbrakk>0/$tr\<rbrakk>)" "$ref \<sharp> pre\<^sub>R P" "$ref \<sharp> cmt\<^sub>R P"
    by (pred_auto)+
  hence "$ref \<sharp> (b &\<^sub>u P)\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: CSP3_iff Guard_def RHS_def R1_def R2c_def R2s_def R3h_def design_def unrest usubst)
  thus ?thesis
    by (metis CSP3_intro CSP_Guard)
qed

lemma CSP4_Guard [closure]:
  assumes "P is CSP" "P is CSP4"
  shows "b &\<^sub>u P is CSP4"
proof (rule CSP4_tri_intro[OF CSP_Guard])
  show "(\<not> pre\<^sub>R (b &\<^sub>u P)) ;; R1 true = (\<not> pre\<^sub>R (b &\<^sub>u P))"
  proof -
    have a:"(\<not> pre\<^sub>R P) ;; R1 true = (\<not> pre\<^sub>R P)"
      by (simp add: CSP4_neg_pre_unit assms(1) assms(2))
    have "(\<not> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P)) ;; R1 true = (\<not> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P))"
    proof -
      have 1:"(\<not> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P)) = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (\<not> pre\<^sub>R P))"
        by (rel_auto)
      also have 2:"... = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> ((\<not> pre\<^sub>R P) ;; R1 true))"
        by (simp add: a)
      also have 3:"... = (\<not> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P)) ;; R1 true"
        by (rel_auto)
      finally show ?thesis .. 
    qed
    thus ?thesis
      by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro NSRD_wait'_unrest_pre
                    NSRD_st'_unrest_pre NSRD_st'_unrest_peri assms unrest)
  qed
  show "$st\<acute> \<sharp> peri\<^sub>R (b &\<^sub>u P)"
    by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro NSRD_wait'_unrest_pre NSRD_st'_unrest_pre
                  NSRD_st'_unrest_peri assms unrest)
  show "$ref\<acute> \<sharp> post\<^sub>R (b &\<^sub>u P)"
    by (simp add: preR_Guard postR_Guard NSRD_CSP4_intro NSRD_wait'_unrest_pre
                  CSP4_ref'_unrest_pre CSP4_ref'_unrest_post assms unrest)
qed
  
lemma NCSP_Guard [closure]:
  assumes "P is NCSP"
  shows "b &\<^sub>u P is NCSP"
proof -
  have "P is CSP"
    using NCSP_implies_CSP assms by blast
  then show ?thesis
    by (metis (no_types) CSP3_Guard CSP3_commutes_CSP4 CSP4_Guard CSP4_Idempotent CSP_Guard Healthy_Idempotent Healthy_def NCSP_def assms comp_apply)
qed
  
subsection {* Sequential Process Laws *}
  
lemma Stop_left_zero:
  assumes "P is CSP"
  shows "Stop ;; P = Stop"
  by (simp add: NSRD_seq_post_false assms NCSP_implies_NSRD NCSP_Stop postR_Stop)

lemma AssignsCSP_id: "\<langle>id\<rangle>\<^sub>C = Skip"
  by (rel_auto)
    
lemma Guard_rdes_def:
  assumes "$ok\<acute> \<sharp> P"
  shows "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
proof -
  have "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q)) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: Guard_def)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
     by (simp add: R1_R2c_commute R1_disj R1_extend_conj' R1_idem R2c_and R2c_disj R2c_idem)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: usubst)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> (pre\<^sub>s \<dagger> (\<not> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rel_auto)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> (pre\<^sub>s \<dagger> (\<not> P)))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> P)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
   proof -
     from assms have "(\<not> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s false, $wait \<mapsto>\<^sub>s false] \<dagger> P) = (\<not> [$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> P)"
       by (rel_auto)
     thus ?thesis by (simp add: usubst)
   qed
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
   finally show ?thesis .
qed
  
lemma Guard_comp:
  "g &\<^sub>u h &\<^sub>u P = (g \<and> h) &\<^sub>u P"
  by (rule antisym, rel_blast, rel_blast)
    
lemma Guard_false [simp]: "false &\<^sub>u P = Stop"
  by (simp add: Guard_def Stop_def alpha)

lemma Guard_true [simp]:
  "P is CSP \<Longrightarrow> true &\<^sub>u P = P"
  by (simp add: Guard_def alpha SRD_reactive_design_alt)

lemma ExtChoice_rdes:
  assumes "\<And> i. $ok\<acute> \<sharp> P(i)" "A \<noteq> {}"
  shows "(\<box>i\<in>A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) = \<^bold>R\<^sub>s((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> Q(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> Q(i))))"
proof -
  have "(\<box>i\<in>A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> pre\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))))"
    by (simp add: ExtChoice_def)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> \<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P(i))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> \<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P(i))))) \<turnstile>
            R1(R2c
            ((\<Squnion>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> \<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P(i))))) \<turnstile>
            R1(R2c
            ((\<Squnion>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))))"
    by (simp add: R2c_UINF R2c_condr R1_cond R1_idem R1_R2c_commute R2c_idem R1_UINF assms R1_USUP R2c_USUP)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> \<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P(i))))) \<turnstile>
            cmt\<^sub>s \<dagger>
            ((\<Squnion>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> \<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P(i))))) \<turnstile>
            cmt\<^sub>s \<dagger>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: usubst)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> \<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P(i))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((\<not> R1(R2c(\<Sqinter>i\<in>A \<bullet> (pre\<^sub>s \<dagger> (\<not> P(i)))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: not_USUP R1_USUP R2c_USUP assms)
  also have "... =
        \<^bold>R\<^sub>s ((\<not> R2c(\<Sqinter>i\<in>A \<bullet> (pre\<^sub>s \<dagger> (\<not> P(i))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: RHS_design_neg_R1_pre)
  also have "... =
        \<^bold>R\<^sub>s ((\<not> (\<Sqinter>i\<in>A \<bullet> (pre\<^sub>s \<dagger> (\<not> P(i))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (metis (no_types, lifting) R2c_not RHS_design_R2c_pre)
  also have "... =
        \<^bold>R\<^sub>s (([$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> (\<not> (\<Sqinter>i\<in>A \<bullet> (\<not> P(i))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
  proof -
    from assms have "\<And> i. pre\<^sub>s \<dagger> (\<not> P(i)) = [$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> (\<not> P(i))"
      by (rel_auto)
    thus ?thesis
      by (simp add: usubst)
  qed
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: rdes_export_pre not_USUP)
  also have "... = \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> Q(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> Q(i))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto, blast+)

  finally show ?thesis .
qed

lemma ExtChoice_tri_rdes:
  assumes "\<And> i . $ok\<acute> \<sharp> P\<^sub>1(i)" "A \<noteq> {}"
  shows "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
proof -
  have "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> ((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: ExtChoice_rdes assms)
  also
  have "... =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> ((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: conj_comm)
  also
  have "... =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: cond_conj wait'_cond_def)
  also
  have "... = \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma ExtChoice_tri_rdes_def:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "ExtChoice A = \<^bold>R\<^sub>s ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<turnstile> (((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)))"
proof -
  have "((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P)) =
        (((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P))"
    by (rel_auto)
  also have "... = (((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P))"
    by (rel_auto)
  finally show ?thesis
    by (simp add: ExtChoice_def)
qed

lemma ExtChoice_empty: "ExtChoice {} = Stop"
  by (simp add: ExtChoice_def cond_def Stop_def)

lemma ExtChoice_single:
  "P is CSP \<Longrightarrow> ExtChoice {P} = P"
  by (simp add: ExtChoice_def usup_and uinf_or SRD_reactive_design_alt cond_idem)

(* Small external choice as an indexed big external choice *)

lemma extChoice_alt_def:
  "P \<box> Q = (\<box>i::nat\<in>{0,1} \<bullet> P \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q)"
  by (simp add: extChoice_def ExtChoice_def, unliteralise, simp)

lemma extChoice_rdes:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
proof -
  have "(\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s (P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> \<^bold>R\<^sub>s (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = (\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s ((P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> (Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp only: RHS_cond R2c_lit)
  also have "... = (\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s ((P\<^sub>1 \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q\<^sub>2)))"
    by (simp add: design_condr)
  also have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
    apply (subst ExtChoice_rdes, simp_all add: assms unrest)
    apply unliteralise
    apply (simp add: uinf_or usup_and)
  done
  finally show ?thesis by (simp add: extChoice_alt_def)
qed

lemma extChoice_tri_rdes:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
         \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
        \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: extChoice_rdes assms)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: conj_comm)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile>
               (((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)) \<diamondop> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: cond_conj wait'_cond_def)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma CSP_ExtChoice [closure]:
  "ExtChoice A is CSP"
  by (simp add: ExtChoice_def RHS_design_is_SRD unrest)

lemma CSP_extChoice [closure]:
  "P \<box> Q is CSP"
  by (simp add: CSP_ExtChoice extChoice_def)
    
lemma preR_ExtChoice [rdes]:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "pre\<^sub>R(ExtChoice A) = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P))"
proof -
  have "pre\<^sub>R (ExtChoice A) = (\<not> R1 (R2c (\<not> (\<Squnion> P\<in>A \<bullet> pre\<^sub>R P))))"
    by (simp add: ExtChoice_def rea_pre_RHS_design usubst unrest)
  also from assms have "... = (\<not> R1 (R2c (\<not> (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(CSP(P)))))))"
    by (metis USUP_healthy)
  also have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(CSP(P))))"
    by (rel_auto)
  also from assms have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(P)))"
    by (metis USUP_healthy)
  finally show ?thesis .
qed

lemma periR_ExtChoice [rdes]:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "peri\<^sub>R(ExtChoice A) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P)) \<Rightarrow> ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)))"
proof -
  have "peri\<^sub>R (ExtChoice A) = peri\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<turnstile>
                                       ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                                       (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: ExtChoice_tri_rdes_def assms)

  also have "... = peri\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R (CSP P)) \<turnstile>
                             ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R (CSP P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R (CSP P))) \<diamondop>
                              (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])

  also have "... = R1 (R2c ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow>
                            (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (CSP P))
                             \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                            (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (CSP P))))"
  proof -
    have "(\<Squnion> P\<in>A \<bullet> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s true] \<dagger> pre\<^sub>R (CSP P))
         = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P))"
      by (rule USUP_cong, simp add: usubst unrest assms)
    thus ?thesis
      by (simp add: rea_peri_RHS_design Healthy_Idempotent SRD_Idempotent usubst unrest assms)
  qed
  also have "... = R1 ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow>
                       (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (CSP P))
                          \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                       (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (CSP P)))"
    by (simp add: R2c_impl R2c_condr R2c_UINF R2c_preR R2c_periR Healthy_Idempotent SRD_Idempotent
                  R2c_tr'_minus_tr R2c_USUP)
  also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow> (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (CSP P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (CSP P)))"
    by (rel_blast)
  finally show ?thesis
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])
qed

lemma postR_ExtChoice [rdes]:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "post\<^sub>R(ExtChoice A) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P)) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P))"
proof -
  have "post\<^sub>R (ExtChoice A) = post\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<turnstile>
                                       ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                                       (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: ExtChoice_tri_rdes_def assms)

  also have "... = post\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R (CSP P)) \<turnstile>
                             ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                              (\<Sqinter> P \<in> A \<bullet> post\<^sub>R (CSP P))))"
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])

  also have "... = R1 (R2c ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (CSP P))))"
  proof -
    have "(\<Squnion> P\<in>A \<bullet> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s false] \<dagger> pre\<^sub>R (CSP P))
         = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P))"
      by (rule USUP_cong, simp add: usubst unrest assms)
    thus ?thesis
      by (simp add: rea_post_RHS_design Healthy_Idempotent SRD_Idempotent usubst unrest assms)
  qed
  also have "... = R1 ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (CSP P)))"
    by (simp add: R2c_impl R2c_condr R2c_UINF R2c_preR R2c_postR Healthy_Idempotent SRD_Idempotent
                  R2c_tr'_minus_tr R2c_USUP)
  also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (CSP P)))"
    by (rel_blast)
  finally show ?thesis
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])
qed

lemma preR_extChoice [rdes]:
  assumes "P is CSP" "Q is CSP" "$wait\<acute> \<sharp> pre\<^sub>R(P)" "$wait\<acute> \<sharp> pre\<^sub>R(Q)"
  shows "pre\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q))"
  by (simp add: extChoice_def preR_ExtChoice assms usup_and)

lemma periR_extChoice [rdes]:
  assumes "P is CSP" "Q is CSP" "$wait\<acute> \<sharp> pre\<^sub>R(P)" "$wait\<acute> \<sharp> pre\<^sub>R(Q)"
  shows "peri\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q) \<Rightarrow> (peri\<^sub>R(P) \<and> peri\<^sub>R(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>R(P) \<or> peri\<^sub>R(Q)))"
  using assms
  by (simp add: extChoice_def, subst periR_ExtChoice, auto simp add: usup_and uinf_or)

lemma postR_extChoice [rdes]:
  assumes "P is CSP" "Q is CSP" "$wait\<acute> \<sharp> pre\<^sub>R(P)" "$wait\<acute> \<sharp> pre\<^sub>R(Q)"
  shows "post\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q) \<Rightarrow> (post\<^sub>R(P) \<or> post\<^sub>R(Q)))"
  using assms
  by (simp add: extChoice_def, subst postR_ExtChoice, auto simp add: usup_and uinf_or)
    
lemma ExtChoice_cong:
  assumes "\<And> P. P \<in> A \<Longrightarrow> F(P) = G(P)"
  shows "(\<box> P\<in>A \<bullet> F(P)) = (\<box> P\<in>A \<bullet> G(P))"
  using assms image_cong by force
    
lemma ref_unrest_ExtChoice:
  assumes 
    "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P)"
    "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> cmt\<^sub>R(P)"    
  shows "$ref \<sharp> (ExtChoice A)\<lbrakk>false/$wait\<rbrakk>"
proof -
  have "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P\<lbrakk>0/$tr\<rbrakk>)"
    using assms by (rel_auto)
  with assms show ?thesis
    by (simp add: ExtChoice_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)
qed

lemma CSP4_set_unrest_wait':
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
  shows "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  fix P
  assume "P \<in> A"
  hence "P is NSRD"
    using NSRD_CSP4_intro assms(1) assms(2) by blast
  thus "$wait\<acute> \<sharp> pre\<^sub>R(P)"
    using NSRD_wait'_unrest_pre by blast
qed

lemma CSP4_set_unrest_st':
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
  shows "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  fix P
  assume "P \<in> A"
  hence "P is NSRD"
    using NSRD_CSP4_intro assms(1) assms(2) by blast
  thus "$st\<acute> \<sharp> pre\<^sub>R(P)"
    using NSRD_st'_unrest_pre by blast
qed

lemma CSP4_ExtChoice:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
  shows "ExtChoice A is CSP4"
proof (cases "A = {}")
  case True thus ?thesis
    by (simp add: ExtChoice_empty Healthy_def CSP4_def, simp add: Skip_is_CSP Stop_left_zero)
next
  case False
  have 1:"(\<not> (\<not> pre\<^sub>R (ExtChoice A)) ;; R1 true) = pre\<^sub>R (ExtChoice A)"
  proof -
    have "\<And> P. P \<in> A \<Longrightarrow> (\<not> pre\<^sub>R(P)) ;; R1 true = (\<not> pre\<^sub>R(P))"
      by (metis (no_types, lifting) Ball_Collect CSP4_neg_pre_unit assms(1) assms(2))
    thus ?thesis
      apply (simp add: preR_ExtChoice CSP4_set_unrest_wait' assms not_UINF seq_UINF_distr not_USUP)
      apply (rule USUP_cong)
      apply (simp)
    done
  qed
  have 2: "$st\<acute> \<sharp> peri\<^sub>R (ExtChoice A)"
  proof -
    have a: "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> pre\<^sub>R(P)"
      using CSP4_set_unrest_st' assms(1) assms(2) by blast
    have b: "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> peri\<^sub>R(P)"
      using CSP4_st'_unrest_peri assms(1) assms(2) by blast
    from a b show ?thesis
      apply (subst periR_ExtChoice)
      apply (simp_all add: assms CSP4_set_unrest_st' CSP4_set_unrest_wait')
      apply (rule CSP4_set_unrest_wait'[of A], simp_all add: unrest assms)
    done
  qed
  have 3: "$ref\<acute> \<sharp> post\<^sub>R (ExtChoice A)"
  proof -
    have a: "\<And> P. P \<in> A \<Longrightarrow> $ref\<acute> \<sharp> pre\<^sub>R(P)"
      by (metis (no_types, lifting) Ball_Collect CSP4_ref'_unrest_pre assms(1) assms(2))
    have b: "\<And> P. P \<in> A \<Longrightarrow> $ref\<acute> \<sharp> post\<^sub>R(P)"
      by (metis (no_types, lifting) Ball_Collect CSP4_ref'_unrest_post assms(1) assms(2))
    from a b show ?thesis
      apply (subst postR_ExtChoice)
      apply (simp_all add: assms CSP4_set_unrest_st' CSP4_set_unrest_wait')
      apply (rule CSP4_set_unrest_wait'[of A], simp_all add: unrest assms)
    done
  qed
  show ?thesis
    by (metis "1" "2" "3" CSP4_tri_intro CSP_ExtChoice assms(1) utp_pred.double_compl)
qed
  
lemma CSP4_extChoice [closure]:
  assumes "P is CSP" "Q is CSP" "P is CSP4" "Q is CSP4"
  shows "P \<box> Q is CSP4"
  by (simp add: extChoice_def, rule CSP4_ExtChoice, simp_all add: assms)
    
lemma NCSP_ExtChoice [closure]:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  shows "ExtChoice A is NCSP"
proof (rule NCSP_intro)
  from assms have cls: "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
    using NCSP_implies_CSP NCSP_implies_CSP3 NCSP_implies_CSP4 by blast+  
  have wu: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
    using NCSP_implies_NSRD NSRD_wait'_unrest_pre assms by force
  show 1:"ExtChoice A is CSP"
    by (metis (mono_tags) Ball_Collect CSP_ExtChoice NCSP_implies_CSP assms)
  from cls show "ExtChoice A is CSP3"
    by (rule_tac CSP3_SRD_intro, simp_all add: closure rdes unrest wu assms  1)
  from cls show "ExtChoice A is CSP4"
    by (simp add: CSP4_ExtChoice)      
qed
  
lemma NCSP_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<box> Q is NCSP"
  by (simp add: NCSP_ExtChoice assms extChoice_def)

lemma ExtChoice_comm:
  "P \<box> Q = Q \<box> P"
  by (unfold extChoice_def, simp add: insert_commute)

lemma ExtChoice_idem:
  "P is CSP \<Longrightarrow> P \<box> P = P"
  by (unfold extChoice_def, simp add: ExtChoice_single)

lemma ExtChoice_assoc:
  assumes "P is CSP" "Q is CSP" "R is CSP"
  shows "P \<box> Q \<box> R = P \<box> (Q \<box> R)"
proof -
  have "P \<box> Q \<box> R = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(R) \<turnstile> cmt\<^sub>R(R))"
    by (simp add: SRD_reactive_design_alt assms(1) assms(2) assms(3))
  also have "... =
    \<^bold>R\<^sub>s (((pre\<^sub>R P \<and> pre\<^sub>R Q) \<and> pre\<^sub>R R) \<turnstile>
          (((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<and> cmt\<^sub>R R)
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           ((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<or> cmt\<^sub>R R)))"
    by (simp add: extChoice_rdes unrest)
  also have "... =
    \<^bold>R\<^sub>s (((pre\<^sub>R P \<and> pre\<^sub>R Q) \<and> pre\<^sub>R R) \<turnstile>
          (((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<and> cmt\<^sub>R R)
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
            ((cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<or> cmt\<^sub>R R)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... =
    \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q \<and> pre\<^sub>R R) \<turnstile>
          ((cmt\<^sub>R P \<and> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) )
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           (cmt\<^sub>R P \<or> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))))"
    by (simp add: conj_assoc disj_assoc)
  also have "... =
    \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q \<and> pre\<^sub>R R) \<turnstile>
          ((cmt\<^sub>R P \<and> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           (cmt\<^sub>R P \<or> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> (\<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(R) \<turnstile> cmt\<^sub>R(R)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = P \<box> (Q \<box> R)"
    by (simp add: SRD_reactive_design_alt assms(1) assms(2) assms(3))
  finally show ?thesis .
qed
      
lemma ExtChoice_Stop:
  assumes "Q is CSP"
  shows "Stop \<box> Q = Q"
  using assms    
proof -
  have "Stop \<box> Q = \<^bold>R\<^sub>s (true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Stop_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> ((($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<or> cmt\<^sub>R Q)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> cmt\<^sub>R Q))"
    by (metis (no_types, lifting) cond_def eq_upred_sym neg_conj_cancel1 utp_pred.inf.left_idem)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> cmt\<^sub>R Q)"
    by (simp add: cond_idem)
  also have "... = Q"
    by (simp add: SRD_reactive_design_alt assms)
  finally show ?thesis .
qed

lemma ExtChoice_Chaos:
  assumes "Q is CSP"
  shows "Chaos \<box> Q = Chaos"
proof -
  have "Chaos \<box> Q = \<^bold>R\<^sub>s (false \<turnstile> true) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Chaos_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> true))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> true)"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = Chaos"
    by (simp add: Chaos_def)
  finally show ?thesis .
qed

lemma InputCSP_CSP [closure]: "x?(v:A(v)) \<^bold>\<rightarrow> P(v) is CSP"
  by (simp add: CSP_ExtChoice InputCSP_def)
    
lemma InputCSP_NCSP [closure]: "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> x?(v:A(v)) \<^bold>\<rightarrow> P(v) is NCSP"
  apply (simp add: InputCSP_def)
  apply (rule NCSP_ExtChoice)
  apply (simp add: NCSP_Guard NCSP_PrefixCSP image_Collect_subsetI top_set_def)
done
  
lemma PrefixCSP_RHS_tri_lemma1:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>II\<rceil>\<^sub>R)) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>II\<rceil>\<^sub>R)"
  apply (rel_auto)
  apply (metis append.left_neutral less_eq_list_def prefix_concat_minus zero_list_def)
  apply (simp add: zero_list_def)
  done

lemma PrefixCSP_RHS_tri_lemma2:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<and> \<not> $wait\<acute>) ;; P = (\<exists> $ref \<bullet> P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  using assms
  by (rel_auto, meson, fastforce)

lemma PrefixCSP_RHS_tri_lemma3:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = (\<exists> $ref \<bullet> P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  using assms
  by (rel_auto, meson)
    
lemma preR_PrefixCSP [rdes]:
  assumes "P is CSP" "$ref \<sharp> pre\<^sub>R P"
  shows "pre\<^sub>R(a \<^bold>\<rightarrow> P) = (pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
proof -
  have "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P = (pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
    by (simp add: wpR_def PrefixCSP_RHS_tri_lemma3 R1_neg_preR usubst unrest assms ex_unrest)
  thus ?thesis
    by (simp add: PrefixCSP_def assms closure rdes Healthy_if)
qed

lemma preR_PrefixCSP_NCSP [rdes]:
  assumes "P is NCSP"
  shows "pre\<^sub>R(a \<^bold>\<rightarrow> P) = (pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
  by (simp add: CSP3_unrest_ref(1) NCSP_implies_CSP NCSP_implies_CSP3 assms preR_PrefixCSP)
  
lemma periR_PrefixCSP [rdes]:
  assumes "P is CSP" "P is CSP3" "P is CSP4"
  shows "peri\<^sub>R(a \<^bold>\<rightarrow> P) = 
         ((pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk> \<Rightarrow> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))"
  by (simp add: PrefixCSP_def assms Healthy_if)
     (simp add: assms NSRD_CSP4_intro closure rdes R1_neg_preR PrefixCSP_RHS_tri_lemma3 unrest ex_unrest usubst wpR_def)

lemma postR_PrefixCSP [rdes]:
  assumes "P is CSP" "P is CSP3" "P is CSP4"
  shows "post\<^sub>R(a \<^bold>\<rightarrow> P) = ((pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk> \<Rightarrow> (post\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  by (simp add: PrefixCSP_def assms Healthy_if) (simp add: assms NSRD_CSP4_intro closure rdes R1_neg_preR PrefixCSP_RHS_tri_lemma3 unrest ex_unrest usubst wpR_def)
    
lemma PrefixCSP_RHS_tri:
  assumes "P is CSP" "P is CSP3"
  shows "a \<^bold>\<rightarrow> P =
         \<^bold>R\<^sub>s (((pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
              ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<diamondop> (post\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
proof -
  have "a \<^bold>\<rightarrow> P =
          \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<diamondop> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st)) ;;
          \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (simp add: PrefixCSP_def Healthy_if DoCSP_RHS_tri SRD_reactive_tri_design assms)
  also have "... =
     \<^bold>R\<^sub>s ((\<not> (($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st)) ;; (\<not> pre\<^sub>R P)) \<turnstile>
           ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; peri\<^sub>R P) \<diamondop>
          (($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; post\<^sub>R P))"
    by (simp add: ex_unrest R1_extend_conj R2s_conj R1_R2s_tr'_extend_tr R2s_st'_eq_st RHS_tri_design_composition unrest R1_neg_R2s_pre_RHS R1_R2s_peri_SRD R1_R2s_post_SRD R2s_true R1_false PrefixCSP_RHS_tri_lemma1 assms)
  also have "... =
     \<^bold>R\<^sub>s (((pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
          ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<diamondop> (post\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
    by (simp add: ex_unrest assms PrefixCSP_RHS_tri_lemma2 PrefixCSP_RHS_tri_lemma3 unrest usubst)
  finally show ?thesis .
qed
  
lemma preR_InputCSP [rdes]: 
  assumes "\<And> v. P(v) is NCSP"
  shows "pre\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) = (\<Squnion> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R (P v)\<lbrakk>$tr ^\<^sub>u \<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)"
  by (simp add: InputCSP_def rdes closure assms usubst unrest, rel_auto)

lemma periR_InputCSP [rdes]: 
  assumes "\<And> v. P(v) is NCSP"
  shows "peri\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) = 
          (pre\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) \<Rightarrow>
            (\<Squnion> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<Rightarrow> ((a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R (P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)) 
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
            (\<Sqinter> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<and> (peri\<^sub>R(P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)))"
  using assms by (simp add: InputCSP_def rdes closure assms usubst unrest, rel_blast)

lemma postR_InputCSP [rdes]: 
  assumes "\<And> v. P(v) is NCSP"
  shows "post\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) = 
          (pre\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) \<Rightarrow> (\<Sqinter> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<and> (post\<^sub>R(P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)))"
  using assms by (simp add: InputCSP_def rdes closure assms usubst unrest, rel_blast)  
  

    (*
lemma 
  assumes "A is NCSP"
  shows "(\<guillemotleft>xa\<guillemotright> =\<^sub>u v) &\<^sub>u x.(\<guillemotleft>xa\<guillemotright>) \<^bold>\<rightarrow> A = x.(v) \<^bold>\<rightarrow> A" (is "?lhs = ?rhs")
proof -
  have "pre\<^sub>R(?lhs) = pre\<^sub>R(?rhs)"
    apply (simp add: rdes closure assms unrest, rel_auto)
*)
  
    
lemma SRD_eq_intro:
  assumes "P is SRD" "Q is SRD" "pre\<^sub>R(P) = pre\<^sub>R(Q)" "peri\<^sub>R(P) = peri\<^sub>R(Q)" "post\<^sub>R(P) = post\<^sub>R(Q)"
  shows "P = Q"
proof -
  have "P = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (simp add: SRD_reactive_tri_design assms(1))
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    by (simp add: assms)
  also have "... = Q"
    by (simp add: SRD_reactive_tri_design assms(2))
  finally show ?thesis .
qed
      
text {* Proof that the input constrained parser version of output is the same as the regular definition. *}
  
lemma output_prefix_is_OutputCSP [simp]:
  assumes "A is NCSP"
  shows "x!(P) \<^bold>\<rightarrow> A = OutputCSP x P A" (is "?lhs = ?rhs")
  by (rule SRD_eq_intro, simp_all add: assms closure rdes, rel_auto+)
    
lemma wpR_extend_tr_NCSP [wp]:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P = (pre\<^sub>R(P))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
proof -
  have "$ref \<sharp> pre\<^sub>R P"
    by (simp add: CSP3_unrest_ref(1) NCSP_implies_CSP NCSP_implies_CSP3 assms)
  thus ?thesis
    by (simp add: wpR_def R1_neg_preR assms closure, rel_auto, blast)
qed
    
lemma tr_extend_peri_lemma:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; peri\<^sub>R P = (peri\<^sub>R(P))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
proof -
  have "$ref \<sharp> peri\<^sub>R P"
    by (simp add: CSP3_unrest_ref(2) NCSP_implies_CSP NCSP_implies_CSP3 assms)
  thus "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; peri\<^sub>R(P) = (peri\<^sub>R(P))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
    by (rel_blast)
qed
     
lemma extChoice_Dist:
  assumes "P is CSP" "S \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "S \<noteq> {}"
  shows "P \<box> (\<Sqinter> S) = (\<Sqinter> Q\<in>S. P \<box> Q)"
proof -
  let ?S1 = "pre\<^sub>R ` S" and ?S2 = "cmt\<^sub>R ` S"
  have "P \<box> (\<Sqinter> S) = P \<box> (\<Sqinter> Q\<in>S \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)))"
    by (simp add: SRD_as_reactive_design[THEN sym] Healthy_SUPREMUM USUP_as_Sup_collect assms)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s((\<Squnion> Q \<in> S \<bullet> pre\<^sub>R(Q)) \<turnstile> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))"
    by (simp add: RHS_design_USUP SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R(P) \<and> (\<Squnion> Q \<in> S \<bullet> pre\<^sub>R(Q))) \<turnstile>
                       ((cmt\<^sub>R(P) \<and> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))
                         \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
                        (cmt\<^sub>R(P) \<or> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s ((\<Squnion> Q\<in>S \<bullet> pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile>
                       (\<Sqinter> Q\<in>S \<bullet> (cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q)))"
    by (simp add: conj_USUP_dist conj_UINF_dist disj_USUP_dist cond_UINF_dist assms)
  also have "... = (\<Sqinter> Q \<in> S \<bullet> \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile>
                                  ((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q))))"
    by (simp add: assms RHS_design_USUP)
  also have "... = (\<Sqinter> Q\<in>S \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = (\<Sqinter> Q\<in>S. P \<box> CSP(Q))"
    by (simp add: USUP_as_Sup_collect, metis (no_types, lifting) Healthy_if SRD_as_reactive_design assms(1))
  also have "... = (\<Sqinter> Q\<in>S. P \<box> Q)"
    by (rule SUP_cong, simp_all add: Healthy_subset_member[OF assms(2)])
  finally show ?thesis .
qed

lemma extChoice_dist:
  assumes "P is CSP" "Q is CSP" "R is CSP"
  shows "P \<box> (Q \<sqinter> R) = (P \<box> Q) \<sqinter> (P \<box> R)"
  using assms extChoice_Dist[of P "{Q, R}"] by simp

lemma GuardedChoiceCSP:
  assumes "\<And> x. P(x) is CSP" "\<And> x. P(x) is CSP3" "A \<noteq> {}"
  shows "(\<box> x\<in>A \<^bold>\<rightarrow> P(x)) =
                   \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> pre\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>/$tr\<rbrakk>)) \<turnstile>
                        ((\<Squnion> x\<in>A \<bullet> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u $ref\<acute>)
                           \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                         (\<Sqinter> x\<in>A \<bullet> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>/$tr\<rbrakk>))) \<diamondop>
                      (\<Sqinter> x\<in>A \<bullet> post\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>/$tr\<rbrakk>)))"
proof -
  have "(\<box> x\<in>A \<^bold>\<rightarrow> P(x))
        = \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> (pre\<^sub>R(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
              ((\<Squnion> x\<in>A \<bullet> $tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
              (\<Sqinter> x\<in>A \<bullet> $tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<diamondop>
              (\<Sqinter> x\<in>A \<bullet> (post\<^sub>R(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))"
    by (simp add: PrefixCSP_RHS_tri assms ExtChoice_tri_rdes unrest)
  also
  have "...
        = \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> pre\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<turnstile>
              ((\<Squnion> x\<in>A \<bullet> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
               (\<Sqinter> x\<in>A \<bullet> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))) \<diamondop>
               (\<Sqinter> x\<in>A \<bullet> post\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also
  have "...
        = \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> pre\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<turnstile>
              ((\<Squnion> x\<in>A \<bullet> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R((R1(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
               (\<Sqinter> x\<in>A \<bullet> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))) \<diamondop>
               (\<Sqinter> x\<in>A \<bullet> post\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)))"
  proof -
    from assms(1) have "\<And> x. R1(P x) = P x"
      by (simp add: Healthy_if SRD_healths(1))
     thus ?thesis by (simp)
  qed
  also
  have "...
        = \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> pre\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<turnstile>
              ((\<Squnion> x\<in>A \<bullet> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> x\<in>A \<bullet> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))) \<diamondop>
               (\<Sqinter> x\<in>A \<bullet> post\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis 
    by (simp add: alpha)
qed
    
(*
lemma wpR_thing [wp]:
  assumes "\<And> a. P(a) is NCSP"
  shows "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R (pre\<^sub>R (P(last\<^sub>u($tr))))) = (pre\<^sub>R(P last\<^sub>u($tr)))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<not> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; (\<not> pre\<^sub>R (P last\<^sub>u($tr))))"
    by (simp add: wpR_def R1_neg_preR closure assms)
  also have "... = (\<not> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; (\<exists> $ref \<bullet> (\<not> pre\<^sub>R (P last\<^sub>u($tr)))))"
    by (simp add: ex_unrest unrest assms closure)
  also have "... = (\<not> (\<exists> $ref \<bullet> (\<not> pre\<^sub>R (P last\<^sub>u($tr))))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"      
    by (rel_auto)
  also have "... = ?rhs"
    by (simp add: ex_unrest unrest assms closure usubst)
  finally show ?thesis .
qed   
    
lemma "\<lbrakk> \<And> a. P(a) is NCSP \<rbrakk> \<Longrightarrow> (\<box> x\<in>A \<^bold>\<rightarrow> P(x)) = (\<box> x\<in>A \<^bold>\<rightarrow> Skip) ;; (P x)\<lbrakk>x\<rightarrow>last\<^sub>u($tr)\<rbrakk>"
*)  

text {* A healthiness condition for weakly guarded CSP processes *}

definition [upred_defs]: "Productive(P) = P \<parallel>\<^sub>R \<^bold>R\<^sub>s(true \<turnstile> true \<diamondop> ($tr <\<^sub>u $tr\<acute>))"

lemma Productive_RHS_design_form:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R"
  shows "Productive(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> (R \<and> $tr <\<^sub>u $tr\<acute>))"
  using assms by (simp add: Productive_def RHS_tri_design_par unrest)

lemma Productive_form:
  "Productive(CSP(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
proof -
  have "Productive(CSP(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) \<parallel>\<^sub>R \<^bold>R\<^sub>s(true \<turnstile> true \<diamondop> ($tr <\<^sub>u $tr\<acute>))"
    by (simp add: Productive_def SRD_as_reactive_tri_design)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (simp add: RHS_tri_design_par unrest)
  finally show ?thesis .
qed

lemma Productive_post_refines_tr_increase:
  assumes "P is CSP" "P is Productive" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(P))"
proof -
  have "post\<^sub>R(P) = post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def Productive_form assms(1) assms(2))
  also have "... = R1(R2c(pre\<^sub>R(P) \<Rightarrow> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (simp add: rea_post_RHS_design unrest usubst assms)
  also have "... = R1((pre\<^sub>R(P) \<Rightarrow> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (simp add: R2c_impl R2c_preR R2c_postR R2c_and R2c_tr_less_tr' assms)
  also have "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> ...)"
    by (rel_auto)
  finally show ?thesis .
qed

lemma Productive_DoCSP [closure]:
  "(do\<^sub>C a :: ('\<sigma>, '\<psi>) action) is Productive"
proof -
  have "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<and> $tr\<acute> >\<^sub>u $tr :: ('\<sigma>, '\<psi>) action)
        = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st)"
    by (rel_auto, simp add: Prefix_Order.strict_prefixI')
  hence "Productive(do\<^sub>C a) = do\<^sub>C a"
    by (simp add: Productive_RHS_design_form DoCSP_RHS_tri unrest)
  thus ?thesis
    by (simp add: Healthy_def)
qed
  
lemma Productive_Guard [closure]:
  assumes "P is CSP" "P is Productive" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "b &\<^sub>u P is Productive"
proof -
  have "b &\<^sub>u P = b &\<^sub>u \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_def Productive_form assms(1) assms(2))
  also have "... =
        \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1 (\<not> pre\<^sub>R P)) \<turnstile>
          (R1 (pre\<^sub>R P \<Rightarrow> peri\<^sub>R P) \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> R1 (pre\<^sub>R P \<Rightarrow> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: Guard_tri_design rea_pre_RHS_design rea_peri_RHS_design rea_post_RHS_design unrest assms
                  usubst R2c_preR R2c_not R2c_impl R2c_periR R2c_postR R2c_and R2c_tr_less_tr')
  also have "... = \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P) \<turnstile> (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P) \<and> $tr\<acute> >\<^sub>u $tr))"
    by (rel_auto)
  also have "... = Productive(b &\<^sub>u P)"
    by (simp add: Productive_def Guard_tri_design RHS_tri_design_par unrest)
  finally show ?thesis
    by (simp add: Healthy_def')
qed
  
lemma Productive_intro:
  assumes "P is SRD" "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(P))" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "P is Productive"
proof -
  have P:"\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)) = P"
  proof -
    have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<diamondop> (pre\<^sub>R(P) \<and> post\<^sub>R(P)))"
      by (metis (no_types, hide_lams) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)
    also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<diamondop> (pre\<^sub>R(P) \<and> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
      by (metis assms(2) utp_pred.inf.absorb1 utp_pred.inf.assoc)
    also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
      by (metis (no_types, hide_lams) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)
    finally show ?thesis
      by (simp add: SRD_reactive_tri_design assms(1))
  qed
  thus ?thesis
    by (metis Healthy_def RHS_tri_design_par Productive_def ok'_pre_unrest unrest_true utp_pred.inf_right_idem utp_pred.inf_top_right)
qed
  
lemma Productive_rdes_intro:
  assumes "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> R" "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) is Productive"
proof (rule Productive_intro)
  show "\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R) is SRD"
    by (simp add: RHS_tri_design_is_SRD assms)

  from assms(1) show "($tr\<acute> >\<^sub>u $tr) \<sqsubseteq> (pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R)) \<and> post\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R)))"
    apply (simp add: rea_pre_RHS_design rea_post_RHS_design usubst assms)
    using assms(1) apply (rel_auto)
    using dual_order.strict_iff_order apply fastforce
  done

  show "$wait\<acute> \<sharp> pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R))"
    by (simp add: rea_pre_RHS_design rea_post_RHS_design usubst R1_def R2c_def R2s_def assms unrest)
qed
        
lemma Productive_seq_1 [closure]:
  assumes "P is NCSP" "P is Productive" "Q is NCSP"
  shows "P ;; Q is Productive"
proof -
  have "P ;; Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q)))"
    by (metis Healthy_def NCSP_implies_CSP SRD_reactive_tri_design Productive_form assms(1) assms(2) assms(3))
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) wp\<^sub>R pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; peri\<^sub>R Q)) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; post\<^sub>R Q))"
    by (simp add: RHS_tri_design_composition_wp unrest closure assms wp NSRD_neg_pre_left_zero  SRD_healths R1_neg_preR ex_unrest wpR_def disj_upred_def)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) wp\<^sub>R pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; peri\<^sub>R Q)) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr))"
  proof -
    have "((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; R1(post\<^sub>R Q)) = ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; R1(post\<^sub>R Q) \<and> $tr\<acute> >\<^sub>u $tr)"
      by (rel_auto)
    thus ?thesis
      by (simp add: NCSP_implies_NSRD NSRD_is_SRD R1_post_SRD assms)
  qed
  also have "... is Productive"
    by (rule Productive_rdes_intro, simp_all add: unrest assms closure wpR_def)
  finally show ?thesis .
qed

lemma Productive_seq_2 [closure]:
  assumes "P is NCSP" "Q is NCSP" "Q is Productive"
  shows "P ;; Q is Productive"
proof -
  have "P ;; Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P))) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_def NCSP_implies_CSP SRD_reactive_tri_design Productive_form assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: RHS_tri_design_composition_wp unrest closure assms wp NSRD_neg_pre_left_zero  SRD_healths R1_neg_preR ex_unrest wpR_def disj_upred_def)  
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr) \<and> $tr\<acute> >\<^sub>u $tr))"
  proof -
    have "(R1(post\<^sub>R P) ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr) \<and> $tr\<acute> >\<^sub>u $tr) = (R1(post\<^sub>R P) ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr))"
      by (rel_auto)
    thus ?thesis
      by (simp add: NCSP_implies_NSRD NSRD_is_SRD R1_post_SRD assms)
  qed
  also have "... is Productive"
    by (rule Productive_rdes_intro, simp_all add: unrest assms closure wpR_def)
  finally show ?thesis .
qed
    
lemma Productive_ExtChoice [closure]:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>Productive\<rbrakk>\<^sub>H"
  shows "ExtChoice A is Productive"
proof -
  have 1: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
    using NCSP_implies_NSRD NSRD_wait'_unrest_pre assms(1) by blast
  show ?thesis
  proof (rule Productive_intro, simp_all add: assms closure rdes 1 unrest)
    have "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) = 
          ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Sqinter> P\<in>A \<bullet> (pre\<^sub>R P \<and> post\<^sub>R P)))"
      by (rel_auto)
    moreover have "(\<Sqinter> P\<in>A \<bullet> (pre\<^sub>R P \<and> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> ((pre\<^sub>R P \<and> post\<^sub>R P) \<and> $tr <\<^sub>u $tr\<acute>))"
      by (rule UINF_cong, metis (no_types, lifting) "1" Ball_Collect NCSP_implies_CSP Productive_post_refines_tr_increase assms utp_pred.inf.absorb1)
    
    ultimately show "($tr\<acute> >\<^sub>u $tr) \<sqsubseteq> ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P))"
      by (simp, rel_auto)
  qed
qed 
     
lemma Productive_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP" "P is Productive" "Q is Productive"
  shows "P \<box> Q is Productive"
  by (simp add: extChoice_def Productive_ExtChoice assms)

lemma Productive_PrefixCSP [closure]: "P is NCSP \<Longrightarrow> a \<^bold>\<rightarrow> P is Productive"
  by (simp add: Healthy_if NCSP_DoCSP NCSP_implies_NSRD NSRD_is_SRD PrefixCSP_def Productive_DoCSP Productive_seq_1)
  
lemma Productive_InputCSP [closure]: 
  "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> x?(v:A(v)) \<^bold>\<rightarrow> P(v) is Productive"
  by (auto simp add: InputCSP_def unrest closure intro: Productive_ExtChoice)
    
lemma preR_Productive [rdes]:
  assumes "P is CSP"
  shows "pre\<^sub>R(Productive(P)) = pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(Productive(P)) = pre\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def Productive_form assms)
  thus ?thesis
    by (simp add: rea_pre_RHS_design usubst unrest R2c_not R1_neg_R2c_pre_RHS assms)
qed
  
lemma periR_Productive [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(Productive(P)) = peri\<^sub>R(P)"
proof -
  have "peri\<^sub>R(Productive(P)) = peri\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def NCSP_implies_CSP Productive_form assms)
  also have "... = R1 (R2c (pre\<^sub>R P \<Rightarrow> peri\<^sub>R P))"
    by (simp add: rea_peri_RHS_design usubst unrest R2c_not R1_neg_R2c_pre_RHS assms closure)
  also have "... = (pre\<^sub>R P \<Rightarrow> peri\<^sub>R P)"
    by (simp add: impl_alt_def R2c_disj R1_disj R2c_not R1_conj R2c_and R2c_peri_SRD 
                  R1_peri_SRD R1_neg_R2c_pre_RHS assms closure R1_tr_less_tr' R2c_tr_less_tr')
  finally show ?thesis
    by (simp add: SRD_peri_under_pre assms unrest closure)
qed

lemma postR_Productive [rdes]: 
  assumes "P is NCSP"
  shows "post\<^sub>R(Productive(P)) = (pre\<^sub>R(P) \<Rightarrow> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)"
proof -
  have "post\<^sub>R(Productive(P)) = post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def NCSP_implies_CSP Productive_form assms)
  also have "... = R1 (R2c (pre\<^sub>R P \<Rightarrow> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr))"
    by (simp add: rea_post_RHS_design usubst unrest assms closure)
  also have "... = (pre\<^sub>R P \<Rightarrow> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)"
    by (simp add: impl_alt_def R2c_disj R1_disj R2c_not R1_conj R2c_and R2c_post_SRD 
             R1_post_SRD R1_neg_R2c_pre_RHS assms closure R1_tr_less_tr' R2c_tr_less_tr')
  finally show ?thesis .
qed
  
lemma preR_frame_seq_export:
  assumes "P is NCSP" "P is Productive" "Q is NCSP"
  shows "(pre\<^sub>R P \<and> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q) = (pre\<^sub>R P \<and> (post\<^sub>R P ;; Q))"
proof -
  have "(pre\<^sub>R P \<and> (post\<^sub>R P ;; Q)) = (pre\<^sub>R P \<and> ((pre\<^sub>R P \<Rightarrow> post\<^sub>R P) ;; Q))"
    by (simp add: SRD_post_under_pre assms closure unrest)
  also have "... = (pre\<^sub>R P \<and> (((\<not> pre\<^sub>R P) ;; Q \<or> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)))"
    by (rel_blast)
  also have "... = (pre\<^sub>R P \<and> (((\<not> pre\<^sub>R P) \<or> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)))"      
    by (simp add: NSRD_neg_pre_left_zero assms closure SRD_healths)
  also have "... = (pre\<^sub>R P \<and> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)"
    by (rel_blast)
  finally show ?thesis ..
qed

(*
lemma ExtChoice_seq_distr:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>Productive\<rbrakk>\<^sub>H" "A \<noteq> {}" "Q is NCSP"
  shows "(\<box> P\<in>A \<bullet> P) ;; Q = (\<box> P\<in>A \<bullet> P ;; Q)"    
proof -   
  have [closure]: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
    by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_wait'_unrest_pre assms(1))
  have [closure]: "(\<lambda>P. NCSP(P) ;; Q) ` A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
    by (auto simp add: Healthy_if closure assms(1) assms(4))
  have nc2: "(\<box> P\<in>A \<bullet> P ;; Q) = (\<box> P\<in>A \<bullet> NCSP(P) ;; Q)"
    by (rule_tac ExtChoice_cong, simp add: Healthy_if closure assms)

  have p1: "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) wp\<^sub>R pre\<^sub>R Q = 
            (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R P \<Rightarrow> post\<^sub>R P) wp\<^sub>R pre\<^sub>R Q)"
      by (simp add: UINF_impl[THEN sym] wp)
    also have "... = (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)"
      by (rule USUP_cong, simp add: SRD_post_under_pre closure assms Healthy_if)
    finally show ?thesis .
  qed
    
  have p2: "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)"
  proof -
    have "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R P \<Rightarrow> post\<^sub>R P)"
      by (rel_auto)
    also have "... = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)"
      by (rule UINF_cong, simp add:  SRD_post_under_pre assms(1) closure)    
    finally show ?thesis .
  qed

  -- {* We perform the proof by showing the pre-, peri- and postconditions are the same *}
      
  have pre: "pre\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = pre\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)"
  proof -
    have "pre\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) wp\<^sub>R pre\<^sub>R Q)"
      by (simp add: rdes closure assms wp)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q))"
      by (simp add: p1)
    also have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R P \<and> (post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)))"    
      by (rel_blast)
    also have "... = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P) \<and> post\<^sub>R (NCSP P) wp\<^sub>R pre\<^sub>R Q)"
      by (rule USUP_cong, simp add: closure assms Healthy_if)
    also have "... = pre\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)"
      by (simp add: rdes closure assms nc2)
    finally show ?thesis .
  qed
      
  have peri: "peri\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = peri\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)" (is "?lhs = ?rhs")
    apply (simp_all add: rdes nc2 closure assms p1 spec_cond_dist)
  proof -
    have "?rhs = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  (\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q \<Rightarrow> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                   (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q \<Rightarrow> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
        apply (simp_all add: rdes nc2 closure assms p1 spec_cond_dist unrest)
        apply (subst USUP_healthy[of "A" "NCSP", THEN sym], simp add: assms)+
        apply (subst UINF_healthy[of "A" "NCSP", THEN sym], simp add: assms)+
        apply (simp)
    done
    also 
    have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                   (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (rel_blast)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> 
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (simp add: spec_cond_dist[THEN sym] UINF_conj_UINF)      
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> pre\<^sub>R P \<and> (post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> 
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (rel_auto)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> pre\<^sub>R P \<and> ((post\<^sub>R P \<and> $tr <\<^sub>u $tr\<acute>) ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> 
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      oops
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
                  ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P) ;; peri\<^sub>R Q))"
      apply (rel_simp, safe)
      apply blast+
      apply meson+

    
        
    have "?lhs = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
                  ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P) ;; peri\<^sub>R Q))"
      by (simp_all add: rdes nc2 closure assms p1 spec_cond_dist, simp add: p2, rel_auto)
    (*
"     ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
     ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
     ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) ;; peri\<^sub>R Q)" *)
      
      
    apply (subst rdes)
    apply (simp_all add: closure assms)
*)
    
lemma PrefixCSP_dist:
  "a \<^bold>\<rightarrow> (P \<sqinter> Q) = (a \<^bold>\<rightarrow> P) \<sqinter> (a \<^bold>\<rightarrow> Q)"
  using Continuous_Disjunctous Disjunctuous_def PrefixCSP_Continuous by auto
    
lemma DoCSP_is_Prefix:
  "do\<^sub>C(a) = a \<^bold>\<rightarrow> Skip"
  by (simp add: PrefixCSP_def Healthy_if closure, metis CSP4_DoCSP CSP4_def Healthy_def)

lemma Prefix_CSP_seq: 
  assumes "P is CSP" "Q is CSP"
  shows "(a \<^bold>\<rightarrow> P) ;; Q = (a \<^bold>\<rightarrow> (P ;; Q))"
  by (simp add: PrefixCSP_def seqr_assoc Healthy_if assms closure)

subsection {* Guarded recursion *}

text {* Proofs that guarded recursion yields a unique fixed-point *}                            

text {* Guardedness variant *}

abbreviation gvrt :: "(('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) chain" where 
"gvrt(n) \<equiv> ($tr \<le>\<^sub>u $tr\<acute> \<and> #\<^sub>u(tt) <\<^sub>u \<guillemotleft>n\<guillemotright>)"
  
lemma gvrt_chain: "chain gvrt"
  apply (simp add: chain_def, safe)
  apply (rel_simp)
  apply (rel_simp)+
done
      
lemma gvrt_limit: "\<Sqinter> (range gvrt) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto)

definition Guarded :: "(('\<sigma>,'\<phi>) action \<Rightarrow> ('\<sigma>,'\<phi>) action) \<Rightarrow> bool" where
"Guarded(F) = (\<forall> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)))"
    
lemma GuardedI: "\<lbrakk> \<And> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)) \<rbrakk> \<Longrightarrow> Guarded F"
  by (simp add: Guarded_def)

theorem guarded_fp_uniq:
  assumes "mono F" "F \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H" "Guarded F"
  shows "\<mu> F = \<nu> F"
proof -
  have "constr F gvrt"
    using assms by (auto simp add: constr_def gvrt_chain Guarded_def)
  hence "($tr \<le>\<^sub>u $tr\<acute> \<and> \<mu> F) = ($tr \<le>\<^sub>u $tr\<acute> \<and> \<nu> F)"
    apply (rule constr_fp_uniq)
    apply (simp add: assms)
    using gvrt_limit apply blast
  done
  moreover have "($tr \<le>\<^sub>u $tr\<acute> \<and> \<mu> F) = \<mu> F"
  proof -
    have "\<mu> F is R1"
      by (rule SRD_healths(1), rule Healthy_mu, simp_all add: assms)
    thus ?thesis
      by (metis Healthy_def R1_def conj_comm)
  qed
  moreover have "($tr \<le>\<^sub>u $tr\<acute> \<and> \<nu> F) = \<nu> F"
  proof -
    have "\<nu> F is R1"
      by (rule SRD_healths(1), rule Healthy_nu, simp_all add: assms)
    thus ?thesis
      by (metis Healthy_def R1_def conj_comm)
  qed
  ultimately show ?thesis
    by (simp)
qed
                
lemma Guarded_const [closure]: "Guarded (\<lambda> X. P)"
  by (simp add: Guarded_def)
    
lemma Guarded_if_Productive [closure]:
  fixes P :: "('\<sigma>,'\<phi>) action"
  assumes "P is NCSP" "P is Productive"
  shows "Guarded (\<lambda> X. P ;; CSP(X))"
proof (clarsimp simp add: Guarded_def)
  -- {* We split the proof into three cases corresponding to valuations for ok, wait, and wait'
        respectively. *}
  fix X n
  have a:"(P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>false/$ok\<rbrakk> = 
        (P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>false/$ok\<rbrakk>"
    by (simp add: usubst closure SRD_left_zero_1 assms)
  have b:"((P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> = 
          ((P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk>"
    by (simp add: usubst closure SRD_left_zero_2 assms)
  have c:"((P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>false/$wait\<rbrakk> = 
          ((P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>false/$wait\<rbrakk>"
  proof -
    have 1:"(P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> = 
          (P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
      by (metis (no_types, lifting) Healthy_def R3h_wait_true SRD_healths(3) SRD_idem) 
    have 2:"(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> = 
          (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
    proof -
      have exp:"\<And> Y::('\<sigma>,'\<phi>) action. (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
                  ((((\<not> pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>)) 
                     \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
      proof -
        fix Y :: "('\<sigma>,'\<phi>) action"
        
        have "(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> = 
              ((\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (metis Healthy_def Productive_form assms(1) assms(2) NCSP_implies_CSP)
        also have "... =  
             ((R1(R2c(pre\<^sub>R(P) \<Rightarrow> ($ok\<acute> \<and> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def RD1_def RD2_def usubst unrest assms closure design_def)
        also have "... = 
             (((\<not> pre\<^sub>R(P) \<or> ($ok\<acute> \<and> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: impl_alt_def R2c_disj R1_disj R2c_not R1_neg_R2c_pre_RHS assms closure R2c_and 
                        R1_extend_conj' R2c_ok' R2c_post_SRD R1_tr_less_tr' R2c_tr_less_tr')
        also have "... = 
             ((((\<not> pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> ($ok\<acute> \<and> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: usubst unrest assms closure seqr_or_distl NSRD_neg_pre_left_zero SRD_healths)
        also have "... = 
             ((((\<not> pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        proof -
          have "($ok\<acute> \<and> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> = 
                ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) \<and> $ok\<acute> =\<^sub>u true) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>"
            by (rel_blast)
          also have "... = (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>\<lbrakk>true/$ok\<rbrakk>"
            using seqr_left_one_point[of ok "(post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)" True "(CSP Y)\<lbrakk>false/$wait\<rbrakk>"]
            by (simp add: true_alt_def[THEN sym])
          finally show ?thesis by (simp add: usubst unrest)
        qed
        finally 
        show "(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
                 ((((\<not> pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>)) 
                 \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>" .
      qed
          
      have 1:"((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP X)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<and> gvrt (Suc n)) = 
              ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP (X \<and> gvrt n))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<and> gvrt (Suc n))"
          apply (rel_auto)
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok')
          apply (rule_tac x="tr\<^sub>0" in exI, rule_tac x="st\<^sub>0" in exI, rule_tac x="ref\<^sub>0" in exI)
          apply (simp)
          apply (erule Prefix_Order.strict_prefixE')
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok' z zs)
          apply (simp add: length_minus_list)
          apply (subgoal_tac "length(tr) + length(z # zs) \<le> length(tr')")
          apply auto[1]
          using Prefix_Order.prefix_length_le apply force
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok')
          apply (rule_tac x="tr\<^sub>0" in exI, rule_tac x="st\<^sub>0" in exI, rule_tac x="ref\<^sub>0" in exI)          
          apply (simp)
          apply (erule Prefix_Order.strict_prefixE')
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok' z zs)
          apply (simp add: length_minus_list)
          apply (subgoal_tac "length(tr) + length(z # zs) \<le> length(tr')")
          apply auto[1]
          using Prefix_Order.prefix_length_le apply force
        done
        have 2:"(\<not> pre\<^sub>R P) ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> = (\<not> pre\<^sub>R P) ;; (CSP(X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk>"
          by (simp add: NSRD_neg_pre_left_zero closure assms SRD_healths)
        show ?thesis
          by (simp add: exp 1 2 utp_pred.inf_sup_distrib2)
      qed
        
      show ?thesis
      proof -
      have "(P ;; (CSP X) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<or>
          (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
      by (subst seqr_bool_split[of wait], simp_all add: usubst utp_pred.distrib(4))
      also 
      have "... = ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<or>
                 (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
        by (simp add: 1 2)
      also 
      have "... = ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<or>
                    P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk>) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        by (simp add: usubst utp_pred.distrib(4))
      also have "... = (P ;; (CSP (X \<and> gvrt n)) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        by (subst seqr_bool_split[of wait], simp_all add: usubst)
      finally show ?thesis by (simp add: usubst)
    qed

  qed
  show "(P ;; CSP(X) \<and> gvrt (Suc n)) = (P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))"
    apply (rule_tac bool_eq_splitI[of "in_var ok"])
    apply (simp_all add: a)
    apply (rule_tac bool_eq_splitI[of "in_var wait"])       
    apply (simp_all add: b c)
  done
qed  

lemma PrefixCSP_Guarded [closure]: "Guarded (PrefixCSP a)"
proof -
  have "PrefixCSP a = (\<lambda> X. do\<^sub>C(a) ;; CSP(X))"
    by (simp add: fun_eq_iff PrefixCSP_def)
  thus ?thesis
    using Guarded_if_Productive NCSP_DoCSP Productive_DoCSP by auto
qed

lemma ExtChoice_Guarded [closure]:
  assumes  "\<And> P. P \<in> A \<Longrightarrow> Guarded P"
  shows "Guarded (\<lambda> X. \<box>P\<in>A \<bullet> P(X))"
proof (rule GuardedI)
  fix X n
  have "\<And> Y. ((\<box>P\<in>A \<bullet> P Y) \<and> gvrt(n+1)) = ((\<box>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    fix Y
    let ?lhs = "((\<box>P\<in>A \<bullet> P Y) \<and> gvrt(n+1))" and ?rhs = "((\<box>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
    have a:"?lhs\<lbrakk>false/$ok\<rbrakk> = ?rhs\<lbrakk>false/$ok\<rbrakk>"
      by (rel_auto)
    have b:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk>"
      by (rel_auto)
    have c:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk>"    
      by (simp add: ExtChoice_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest, rel_blast)
    show "?lhs = ?rhs"
      using a b c
      by (rule_tac bool_eq_splitI[of "in_var ok"], simp, rule_tac bool_eq_splitI[of "in_var wait"], simp_all)
  qed
  moreover have "((\<box>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) \<and> gvrt(n+1)) =  ((\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    have "(\<box>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) = (\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1)))"
    proof (rule ExtChoice_cong)
      fix P assume "P \<in> A"
      thus "(P X \<and> gvrt(n+1)) = (P (X \<and> gvrt(n)) \<and> gvrt(n+1))"
        using Guarded_def assms by blast
    qed
    thus ?thesis by simp
  qed
  ultimately show "((\<box>P\<in>A \<bullet> P X) \<and> gvrt(n+1)) = ((\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)))) \<and> gvrt(n+1))"
    by simp
qed

lemma extChoice_Guarded [closure]:
  assumes "Guarded P" "Guarded Q"
  shows "Guarded (\<lambda> X. P(X) \<box> Q(X))"
proof -
  have "Guarded (\<lambda> X. \<box>F\<in>{P,Q} \<bullet> F(X))"
    by (rule ExtChoice_Guarded, auto simp add: assms)
  thus ?thesis
    by (simp add: extChoice_def)
qed
  
lemma Continuous_mu_CSP_form_1 [closure]: "Continuous (\<lambda>X. P ;; CSP X)"
  using SRD_Continuous 
  by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], rename_tac A, drule_tac x="A" in spec, simp)

lemma mu_CSP_form_1_type [closure]: 
  assumes "P is CSP"
  shows "(\<lambda>X. P ;; CSP X) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  by (blast intro: funcsetI closure assms)
  
text {* Example fixed-point calculation *}
  
lemma mu_csp_form_1 [rdes]: 
  assumes "P is NCSP" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; CSP(X)) = (\<Sqinter>i \<bullet> P \<^bold>^ (i+1)) ;; Miracle"
proof -
  have 1:"Continuous (\<lambda>X. P ;; CSP X)"
    using SRD_Continuous 
    by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], drule_tac x="A" in spec, simp)
  have 2: "(\<lambda>X. P ;; CSP X) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
    by (blast intro: funcsetI closure assms)
  with 1 2 have "(\<mu> X \<bullet> P ;; CSP(X)) = (\<nu> X \<bullet> P ;; CSP(X))"
    by (simp add: guarded_fp_uniq Guarded_if_Productive[OF assms] Continuous_Monotonic funcsetI closure)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ i) false)"
    by (simp add: sup_continuous_lfp 1 sup_continuous_Continuous false_upred_def) 
  also have "... = ((\<lambda>X. P ;; CSP X) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ (i+1)) false)"      
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ (i+1)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1) ;; Miracle)"
  proof (rule SUP_cong,simp_all)
    fix i
    show "P ;; CSP (((\<lambda>X. P ;; CSP X) ^^ i) false) = (P ;; P \<^bold>^ i) ;; Miracle"
    proof (induct i)
      case 0
      then show ?case
        by (simp, metis srdes_hcond_def srdes_theory_continuous.healthy_top)
    next
      case (Suc i)          
      then show ?case
        by (simp add: Healthy_if NCSP_implies_CSP SRD_power_Suc SRD_seqr_closure assms(1) seqr_assoc srdes_theory_continuous.weak.top_closed)
    qed
  qed
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1)) ;; Miracle"
    by (simp add: seq_Sup_distr)    
  finally show ?thesis 
    by (simp add: USUP_as_Sup[THEN sym])
qed
  
lemma mu_example1: "(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = (\<Sqinter>i \<bullet> do\<^sub>C(a) \<^bold>^ (i+1)) ;; Miracle"
  by (simp add: PrefixCSP_def mu_csp_form_1 closure)
    
lemma preR_mu_example1 [rdes]: "pre\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = true"
  by (simp add: mu_example1 rdes closure unrest wp)

lemma periR_mu_example1 [rdes]: 
  "peri\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = 
   (\<Sqinter>x\<in>{0..} \<bullet> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<^bold>^ x ;; ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>))"
  by (simp add: mu_example1 rdes closure unrest wp seq_UINF_distr)

lemma postR_mu_example1 [rdes]: 
  "post\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = false"
  by (simp add: mu_example1 rdes closure unrest wp) 
    
subsection {* Stateless merge Predicate *}

definition CSPMerge' :: "'\<psi> set \<Rightarrow> ((unit,'\<psi>) st_csp) merge" ("N\<^sub>C") where
  [upred_defs]:
  "CSPMerge'(cs) = (
    $ref\<acute> =\<^sub>u ($0-ref \<inter>\<^sub>u $1-ref) \<and>
    $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
    ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u ($0-tr - $tr\<^sub><) \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> ($1-tr - $tr\<^sub><) \<and>
    ($0-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u ($1-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"

lemma CSPMerge'_R2m [closure]: "N\<^sub>C(cs) is R2m"
  by (rel_auto)

lemma CSPMerge'_RDM [closure]: "N\<^sub>C(cs) is RDM"
  by (rule RDM_intro, simp add: closure, simp_all add: CSPMerge'_def unrest)

definition CSPMerge :: "'\<psi> set \<Rightarrow> ((unit,'\<psi>) st_csp) merge" ("M\<^sub>C") where
[upred_defs]: "M\<^sub>C(cs) = M\<^sub>R(N\<^sub>C(cs)) ;; SKIP"
    
subsection {* Parallel Operator *}

text {*
  So we are not considering processes with program state. Is there a way to
  generalise the definition below to cater fro state too? Or are there some
  semantic issues associated with this, beyond merging the state spaces?
*}

abbreviation ParCSP ::
  "'\<theta> rel_csp \<Rightarrow> '\<theta> event set \<Rightarrow> '\<theta> rel_csp \<Rightarrow> '\<theta> rel_csp" (infixr "[|_|]" 105) where
"P [|cs|] Q \<equiv> P \<parallel>\<^bsub>M\<^sub>C(cs)\<^esub> Q"

subsubsection {* CSP Parallel Laws *}
  
lemma parallel_is_CSP:
  assumes "P is CSP" "Q is CSP"
  shows "(P \<parallel>\<^bsub>M\<^sub>C(cs)\<^esub> Q) is CSP"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C(cs))\<^esub> Q) is CSP"
    by (simp add: closure assms)
  hence "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C(cs))\<^esub> Q) ;; SKIP is CSP"
    by (simp add: SKIP_is_Skip closure)
  thus ?thesis
    by (simp add: CSPMerge_def par_by_merge_seq_add)
qed
      
lemma swap_CSPMerge': "(swap\<^sub>m ;; N\<^sub>C(cs)) = N\<^sub>C(cs)"
  apply (rel_auto) using tr_par_sym by blast+
  
theorem parallel_commutative:
  "(P [|cs|] Q) = (Q [|cs|] P)"
  by (simp add: CSPMerge_def par_by_merge_commute seqr_assoc swap_CSPMerge' swap_merge_rd)
  
end