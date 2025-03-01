theory tcircus_rel
  imports "tcircus_traces" "Patience_Tests"
begin

recall_syntax

subsection \<open> Foundations \<close>

text \<open> We don't need a tick event, because this is handled by the $wait$ flag. Nor do we need to
  separate refusals and tocks. A refusal in tock-CSP (as I understand) can occur either (1) just
  before a tock occurs, or (2) at the end of a trace. We gain the former by embedding refusals
  in a tock (as in CML). We gain the latter by including the $ref'$ variable as in Circus. We encode
  the healthiness condition that a tock can't occur in a refusal before a tock event using
  the type system. \<close>


alphabet ('s, 'e) tt_vars = "('e reftrace, 's) rsp_vars" +
  ref :: "('e) refusal" 
  pat :: "bool"

type_synonym ('\<sigma>,'\<phi>) ttcircus = "('\<sigma>, '\<phi>) tt_vars"
type_synonym ('\<sigma>,'\<phi>) taction  = "('\<sigma>, '\<phi>) ttcircus hrel"
type_synonym '\<phi> ttcsp = "(unit,'\<phi>) taction"
type_synonym '\<phi> ttprocess  = "'\<phi> ttcsp hrel"
type_synonym ('a,'\<sigma>,'\<theta>) expr_tc = "('a, ('\<sigma>,'\<theta>) ttcircus \<times> ('\<sigma>,'\<theta>) ttcircus) uexpr"

(*
text \<open> We record patience/urgency via the @{const pat} variable instead of in the refusal set. This
  is so that conjunction works -- time is deterministic, and so a process is patient (accepts
  Tock) only when all subprocesses do. \<close>
*)

(*
text \<open> The $ref$ variable is not simply a set, but a set augmented with the @{term "\<^bold>\<bullet>"} that denotes
  stability. We need this because tick-tock traces can end without a refusal. Note that unlike
  in the trace this is a refusal over @{typ "'e tev"} so that we can refuse tocks at the end. \<close>
definition tc_time :: "('e set, 's) uexpr \<Rightarrow> (nat set, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<T>'(_, _')") where 
[upred_defs]: "\<T>(X, A) = U(\<exists> t \<in> tocks \<lceil>- X\<rceil>\<^sub>S\<^sub><. $tr\<acute> = $tr @ \<guillemotleft>t\<guillemotright> \<and> length(\<guillemotleft>t\<guillemotright>) \<in> \<lceil>A\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)"
text \<open> The interpretation of $wait$ changes to there being both stable (quiescent) and unstable.
  Extra information is needed for refusals. What is the meaning pericondition? \<close>
*)

(* FIXME: Nasty hack below *)

lemma tc_splits:
  "(\<forall>r. P r) = (\<forall>ok wait tr st ref pat more. P \<lparr>ok\<^sub>v = ok, wait\<^sub>v = wait, tr\<^sub>v = tr, st\<^sub>v = st, ref\<^sub>v = ref, pat\<^sub>v = pat, \<dots> = more\<rparr>)"
  "(\<exists>r. P r) = (\<exists> ok wait tr st ref pat more. P \<lparr>ok\<^sub>v = ok, wait\<^sub>v = wait, tr\<^sub>v = tr, st\<^sub>v = st, ref\<^sub>v = ref, pat\<^sub>v = pat, \<dots> = more\<rparr>)"
  by (metis rsp_vars.surjective tt_vars.ext_surjective)+

declare tt_vars.splits [alpha_splits del]
declare des_vars.splits [alpha_splits del]
declare rp_vars.splits [alpha_splits del]
declare rsp_vars.splits [alpha_splits del]
declare tc_splits [alpha_splits]
declare rsp_vars.splits [alpha_splits]
declare rp_vars.splits [alpha_splits]
declare des_vars.splits [alpha_splits]

subsection \<open> Reactive Relation Constructs \<close>

definition tt_skip :: "('s, 'e) taction" ("II\<^sub>t") where
[upred_defs]: "tt_skip = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"

definition sr_skip :: "('s, 'e) taction" ("II\<^sub>s\<^sub>r") where
[upred_defs]: "sr_skip = (($ref\<acute> =\<^sub>u $ref) \<and> ($ok\<acute> =\<^sub>u $ok) \<and> ($wait\<acute> =\<^sub>u $wait) \<and> II\<^sub>t)"

definition TRR1 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR1(P) = (II\<^sub>t ;; P)"

definition TRR2 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR2(P) = (U(($tr\<acute> = $tr) \<and> ($ref\<acute> = \<^bold>\<bullet>) \<and> ($pat\<acute>) \<or> P))"

definition TRR3 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR3(P) = (P ;; II\<^sub>t)"

definition uns :: "('s,'e) taction" where
[upred_defs]: "uns = U($tr\<acute> = $tr \<and> ($ref\<acute> = \<^bold>\<bullet>) \<and> ($pat\<acute>))"

definition TRR4 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR4 P Q = (Q \<or> P ;; uns)"


definition TRR6 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR6(P) = (P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<or> (P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<and> $pat\<acute>))"

(*
definition TRR6a :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR6a(P) = U(P\<lbrakk>\<guillemotleft>false\<^sub>p\<guillemotright>/$pat\<acute>\<rbrakk> \<or> (P \<and> ($wait \<Rightarrow> ($pat\<acute> = true\<^sub>p))))"
*)

definition J6 :: "('s,'e) taction" where
[upred_defs]: "J6 = ((($pat) \<Rightarrow> ($pat\<acute>)) \<and> II\<^sub>s\<^sub>r)"

(*
definition J61 :: "('s,'e) taction" where
[upred_defs]: "J61 = ((($pat =\<^sub>u \<guillemotleft>true\<^sub>p\<guillemotright>) \<Rightarrow> ($pat\<acute> =\<^sub>u \<guillemotleft>true\<^sub>p\<guillemotright>)) \<and> ($ref\<acute> =\<^sub>u $ref) \<and> II\<^sub>t)"
*)

no_utp_lift TRR6 J6

lemma TRR6_idem:
  "TRR6(TRR6(P)) = TRR6 P"
  by (rel_auto)

(*
lemma TRR6_form: "TRR6 P = (P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<or> (P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<and> $pat\<acute>))"
  apply
*)

lemma J6_split:
  shows "(P ;; J6) = TRR6 P"
proof -
  have "(P ;; J6) = (P ;; (($pat \<Rightarrow> $pat\<acute>) \<and> II\<^sub>s\<^sub>r))"
    by (simp add: J6_def)
  also have "\<dots> = (P ;; (($pat \<Rightarrow> $pat \<and> $pat\<acute>) \<and> II\<^sub>s\<^sub>r))"
    by (rel_auto)
  also have "\<dots> = ((P ;; (\<not> $pat \<and> II\<^sub>s\<^sub>r)) \<or> (P ;; ($pat \<and> II\<^sub>s\<^sub>r \<and> $pat\<acute>)))"
    by (rel_auto)
  also have "\<dots> = (P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<or> (P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<and> $pat\<acute>))"
    by (rel_auto)
  also have "\<dots> = TRR6 P"
    by rel_auto
  (* 
  proof -
    have "(P ;; (\<not> $pat \<and> II\<^sub>s\<^sub>r)) = P\<^sup>f"
    proof -
      have "(P ;; (\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D)) = ((P \<and> \<not> $ok\<acute>) ;; \<lceil>II\<rceil>\<^sub>D)"
        by (rel_auto)
      also have "... = (\<exists> $ok\<acute> \<bullet> P \<and> $ok\<acute> =\<^sub>u false)"
        by (rel_auto)
      also have "... = P\<^sup>f"
        by (metis C1 one_point out_var_uvar unrest_as_exists ok_vwb_lens vwb_lens_mwb)
     finally show ?thesis .
    qed
    moreover have "(P ;; ($ok \<and> (\<lceil>II\<rceil>\<^sub>D \<and> $ok\<acute>))) = (P\<^sup>t \<and> $ok\<acute>)"
    proof -
      have "(P ;; ($ok \<and> (\<lceil>II\<rceil>\<^sub>D \<and> $ok\<acute>))) = (P ;; ($ok \<and> II))"
        by (rel_auto)
      also have "... = (P\<^sup>t \<and> $ok\<acute>)"
        by (rel_auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by simp
  qed
  *)
  finally show ?thesis .
qed

lemma TRR6_equivalence:
  "P is TRR6 \<longleftrightarrow> `P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<Rightarrow> P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>`"
proof -
  have "`P \<Leftrightarrow> (P ;; J6)` \<longleftrightarrow> `P \<Leftrightarrow> (P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<or> (P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<and> $pat\<acute>))`"
    by (simp add: J6_split TRR6_def)
  also have "\<dots> \<longleftrightarrow> `(P \<Leftrightarrow> P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<or> P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<and> $pat\<acute>)\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (P \<Leftrightarrow> P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<or> P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<and> $pat\<acute>)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>`"
    by (simp add: subst_bool_split)
  also have "\<dots> = `(P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<Leftrightarrow> P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk>) \<and> (P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<Leftrightarrow> P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<or> P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>)`"
    by (subst_tac)
  also have "\<dots> = `P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<Leftrightarrow> (P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<or> P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>)`"
    by (pred_auto robust)
  also have "\<dots> = `(P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk> \<Rightarrow> P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>)`"
    by (pred_blast)
  finally show ?thesis
    by (metis Healthy_def J6_split taut_iff_eq)
qed

lemma TRR6_equiv:
  "P is TRR6 \<longleftrightarrow> P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk>"
  by (simp add: TRR6_equivalence refBy_order)


lemma TRR6_alt_def:
  "(P is TRR6) = (P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> P)"
  by (smt (verit) Healthy_def TRR6_def TRR6_equiv out_var_semi_uvar pat_vwb_lens subst_conj unrest_as_subst unrest_lit unrest_usubst_single utp_pred_laws.inf.absorb_iff1 utp_pred_laws.inf.idem vwb_lens_mwb)
(*
proof
  assume 1: "P is TRR6"
  have "TRR6(P)\<lbrakk>\<guillemotleft>true\<^sub>p\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> TRR6(P)"         
    by (rel_auto)
  thus "P\<lbrakk>\<guillemotleft>true\<^sub>p\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> P"
    by (simp add: Healthy_if 1)
next
  assume "P\<lbrakk>\<guillemotleft>true\<^sub>p\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> P"
  thus "P is TRR6"
    apply(rel_auto)
    sledgehammer
    by(rel_auto; smt (z3))
qed

lemma TRR6_J6:
  "TRR6(P) = (P ;; J6)"
  apply(rel_auto)
  by (metis (full_types))
*)

lemma [closure]:
  assumes "P is TRR1"
  shows "TRR6(P) is TRR1"
proof - 
  have "TRR1(TRR6(TRR1(P))) = TRR6(TRR1(P))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma [closure]:
  assumes "P is RR"
  shows "TRR6(P) is RR"
proof - 
  have "RR(TRR6(RR(P))) = TRR6(RR(P))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

definition Hpat :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "Hpat(P) = (P \<and> U($pat\<acute>))"

definition Hinsist :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "Hinsist(P) = (\<exists> $pat\<acute> \<bullet> P)"

definition TRRw :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRRw(P) = TRR1(RR(P))"

no_utp_lift TRRw

definition TRR :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR(P) = TRR6(TRRw(P))"

definition TRC :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRC(P) = TRR1(RC(P))"

definition TRF :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRF(P) = TRR3(TRR(P))"

lemma Hpat_idem: "Hpat(Hpat(P)) = Hpat(P)"
  by (rel_blast)

lemma Hinsist_idem: "Hinsist(Hinsist(P)) = Hinsist(P)"
  by (rel_blast)

lemma Hpat_Idempotent [closure]: "Idempotent Hpat"
  by (simp add: Hpat_idem Idempotent_def)

lemma Hinsist_Idempotent [closure]: "Idempotent Hinsist"
  by (simp add: Hinsist_idem Idempotent_def)

lemma Hpat_Continuous [closure]: "Continuous Hpat"
  by (rel_blast)

lemma Hinsist_Continuous [closure]: "Continuous Hinsist"
  by (rel_blast)

lemma TRRw_idem: "TRRw(TRRw(P)) = TRRw(P)"
  by (rel_blast)

lemma TRR_idem: "TRR(TRR(P)) = TRR(P)"
  by (rel_blast)

lemma TRF_idem: "TRF(TRF(P)) = TRF(P)"
  by (rel_blast)

lemma TRR_TRR1_raw: "TRR P is TRR1"
  by (rel_auto)

lemma TRR_Idempotent [closure]: "Idempotent TRR"
  by (simp add: TRR_idem Idempotent_def)

lemma TRF_Idempotent [closure]: "Idempotent TRF"
  by (simp add: TRF_idem Idempotent_def)

lemma TRRw_Idempotent [closure]: "Idempotent TRRw"
  by (simp add: TRRw_idem Idempotent_def)

lemma TRRw_Continuous [closure]: "Continuous TRRw"
  by (rel_blast)

lemma TRR_Continuous [closure]: "Continuous TRR"
  by (rel_blast)

lemma TRR6_Continuous [closure]: "Continuous TRR6"
  by (rel_blast)

lemma TRF_Continuous [closure]: "Continuous TRF"
  by (rel_blast)

lemma TRR_alt_def: "TRR(P :: ('s,'e) taction) = (\<exists> $ref \<bullet> (\<exists> $pat \<bullet> TRR6(RR(P))))"
  by rel_blast

lemma TRRw_alt_def: "TRRw(P :: ('s,'e) taction) = (\<exists> $ref \<bullet> (\<exists> $pat \<bullet> RR(P)))"
  by (rel_auto)

lemma TRRw_intro:
  assumes "$ref \<sharp> P" "$pat \<sharp> P" "P is RR"
  shows "P is TRRw"
  by (metis Healthy_def TRRw_alt_def assms ex_unrest)

lemma TRR_intro:
  assumes "$ref \<sharp> P" "$pat \<sharp> P" "P is RR" "P is TRR6"
  shows "P is TRR"
  by (simp add: TRR_alt_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma TRRw_unrest_ref [unrest]: "P is TRRw \<Longrightarrow> $ref \<sharp> P"
  by (metis (no_types, lifting) Healthy_if TRRw_alt_def exists_twice in_var_uvar ref_vwb_lens unrest_as_exists vwb_lens_mwb)

lemma TRRw_unrest_pat [unrest]: "P is TRRw \<Longrightarrow> $pat \<sharp> P"
  by (metis (no_types, lifting) Healthy_if TRRw_alt_def ex_commute exists_twice in_var_indep in_var_uvar pat_vwb_lens tt_vars.indeps(1) unrest_as_exists vwb_lens.axioms(2))

lemma TRR_unrest_ref [unrest]: "P is TRR \<Longrightarrow> $ref \<sharp> P"
  by (metis (no_types, lifting) Healthy_if TRR_alt_def exists_twice in_var_uvar ref_vwb_lens unrest_as_exists vwb_lens.axioms(2))

lemma TRR_unrest_pat [unrest]: "P is TRR \<Longrightarrow> $pat \<sharp> P"
  by (metis (no_types, lifting) Healthy_if TRR_alt_def ex_commute exists_twice in_var_indep in_var_uvar pat_vwb_lens tt_vars.indeps(1) unrest_as_exists vwb_lens.axioms(2))

lemma TRRw_TRR [closure]:
  assumes "P is TRRw"
  shows "P is TRR1"
proof -
  have "TRRw(P) is TRR1"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRR_TRR1 [closure]:
  assumes "P is TRR"
  shows "P is TRR1"
  by (metis Healthy_if TRR_TRR1_raw assms)

lemma TRR_TRRw [closure]:
  assumes "P is TRR"
  shows "P is TRRw"
proof - 
  have "TRR P is TRRw"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRRw_implies_RR [closure]: 
  assumes "P is TRRw"
  shows "P is RR"
proof -
  have "RR(TRRw(P)) = TRRw(P)"
    by (rel_blast)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma TRR_implies_RR [closure]: 
  assumes "P is TRR"
  shows "P is RR"
proof -
  have "RR(TRR(P)) = TRR(P)"
    by (rel_blast)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma RR_TRR [closure]: "P is RR \<Longrightarrow> TRR P is RR"
  using Healthy_def TRR_idem TRR_implies_RR by auto

lemma TRC_RR_raw: "TRC(P) is RR"
  apply(rel_auto)
  apply(meson eq_iff minus_cancel_le)
  apply(metis (no_types, hide_lams) Prefix_Order.prefixE Prefix_Order.prefixI Prefix_Order.same_prefix_prefix plus_list_def trace_class.add_diff_cancel_left)
  done

lemma TRC_RR [closure]:
  assumes "P is TRC"
  shows "P is RR"
  by (metis Healthy_if TRC_RR_raw assms)

lemma TRC_TRR1_raw [closure]: "TRC(P) is TRRw"
proof -
  have "$pat \<sharp> TRC P" "$ref \<sharp> TRC P"
    by (rel_auto)+
  thus "TRC P is TRRw"
    by (simp add: TRC_RR_raw TRRw_intro)
qed

lemma TRC_TRR1 [closure]:
  assumes "P is TRC"
  shows "P is TRRw"
  by (metis Healthy_if TRC_TRR1_raw assms)

lemma TRC_TRR6 [closure]:
  assumes "P is TRC"
  shows "P is TRR6"
proof -
  have "TRC(P) is TRR6"
    apply(rel_auto)
    apply(meson)
    done
  thus "P is TRR6"
    by (simp add: Healthy_if assms)
qed

lemma TRC_implies_TRR [closure]:
  assumes "P is TRC"
  shows "P is TRR"
  by (simp add: Healthy_if Healthy_intro TRC_RR TRC_TRR1 TRC_TRR6 TRR_def assms)

lemma TRC_RC2_raw [closure]: "TRC(P) is RC2"
  by (rel_auto, blast)

lemma TRC_implies_RC2 [closure]:
  assumes "P is TRC"
  shows "P is RC2"
  by (metis Healthy_if TRC_RC2_raw assms)

lemma TRC_implies_RC [closure]: "P is TRC \<Longrightarrow> P is RC"
  by (simp add: RC_intro_prefix_closed TRC_implies_RC2 TRC_implies_TRR TRR_implies_RR)

lemma TRC_idem: 
  assumes "P is TRR"
  shows "TRC (TRC P) = TRC P"
proof -
  have 1: "TRC P is RC"
    apply(rule RC_intro_prefix_closed)
    using TRC_RR_raw apply blast
    by (simp add: TRC_RC2_raw)
  have "TRC(TRC P) = TRR1(RC(TRC P))"
    by (meson TRC_def)
  also have "\<dots> = TRR1(TRC P)"
    by (simp add: "1" Healthy_if)
  also have "\<dots> = TRC P"
    by (meson Healthy_if TRC_TRR1_raw TRRw_TRR)
  finally show "TRC(TRC P) = TRC P" .
qed

lemma TRR_closed_TRC [closure]: "TRC(P) is TRR"
  by (metis Healthy_if Healthy_intro RC_intro_prefix_closed TRC_RC2_raw TRC_RR_raw TRC_TRR1_raw
      TRC_def TRC_implies_TRR TRRw_TRR)

lemma tc_skip_self_unit [simp]: "II\<^sub>t ;; II\<^sub>t = II\<^sub>t"
  by (rel_auto)

lemma TRR_tc_skip [closure]: "II\<^sub>t is TRR"
  by (rel_auto)

lemma TRF_implies_TRR3 [closure]: "P is TRF \<Longrightarrow> P is TRR3"
  by (metis (no_types, hide_lams) Healthy_def RA1 TRF_def TRR3_def tc_skip_self_unit)

lemma TRR6_closed_seq [closure]: "Q is TRR6 \<Longrightarrow> P ;; Q is TRR6"
proof -
  assume "Q is TRR6"
  hence 1: "P ;; Q = P ;; TRR6 Q"
    by (simp add: Healthy_if)
  also have "\<dots> = TRR6(P ;; TRR6 Q)"
    by rel_blast
  also have "\<dots> = TRR6(P ;; Q)"
    by (simp add: 1)
  finally have "P ;; Q = TRR6(P ;; Q)" .
  thus ?thesis
    by (metis Healthy_intro)
qed

lemma TRRw_closed_seq [closure]: "\<lbrakk> P is TRRw; Q is TRRw \<rbrakk> \<Longrightarrow> P ;; Q is TRRw"
  by (metis (no_types, hide_lams) Healthy_if Healthy_intro RA1 RR_idem TRR1_def TRR_implies_RR TRR_tc_skip TRRw_def seq_RR_closed)

lemma TRR_closed_seq [closure]: "\<lbrakk> P is TRR; Q is TRR \<rbrakk> \<Longrightarrow> P ;; Q is TRR"
  by (metis (no_types, hide_lams) Healthy_if Healthy_intro TRR6_closed_seq TRR6_idem TRR_def TRR_implies_RR TRR_intro TRR_unrest_pat TRR_unrest_ref seq_RR_closed unrest_semir_undash)

lemma TRF_implies_TRR [closure]: "P is TRF \<Longrightarrow> P is TRR"
  by (metis Healthy_def TRF_def TRR3_def TRR_closed_seq TRR_idem TRR_tc_skip)

lemma TRR_right_unit: 
  assumes "P is TRR" "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
  shows "P ;; II\<^sub>t = P"
proof -
  have "TRR(\<exists> $ref\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> P) ;; II\<^sub>t = TRR(\<exists> $ref\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> P)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms ex_unrest)
qed

lemma TRF_right_unit [rpred]:
  "P is TRF \<Longrightarrow> P ;; II\<^sub>t = P"
  by (metis Healthy_if TRF_def TRF_implies_TRR TRR3_def)

lemma TRF_intro:
  assumes "P is TRR" "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
  shows "P is TRF"
  by (metis Healthy_def TRF_def TRR3_def assms TRR_right_unit)

lemma TRF_unrests [unrest]:
  assumes "P is TRF"
  shows "$ref\<acute> \<sharp> P"  "$pat\<acute> \<sharp> P"
proof -
  have "$ref\<acute> \<sharp> TRF(P)" "$pat\<acute> \<sharp> TRF(P)"
    by (rel_auto)+
  thus "$ref\<acute> \<sharp> P"  "$pat\<acute> \<sharp> P"
    by (simp_all add: Healthy_if assms)
qed

lemma TRR_TRF [closure]: "P is TRR \<Longrightarrow> TRF(P) is TRR"
  by (simp add: Healthy_if TRF_def TRR3_def TRR_closed_seq TRR_tc_skip)

lemma TRR_TRR3 [closure]: "P is TRR \<Longrightarrow> TRR3(P) is TRR"
  by (simp add: Healthy_if TRR3_def TRR_closed_seq TRR_tc_skip)

lemma TRF_tc_skip [closure]: "II\<^sub>t is TRF"
  by rel_auto

no_utp_lift RR TRR TRF TRR1

lemma TRR_transfer_refine:
  fixes P Q :: "('s, 'e) taction"
  assumes "P is TRR" "Q is TRR" 
    "(\<And> t s s' r p. U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> P) 
                   \<sqsubseteq> U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> Q))"
  shows "P \<sqsubseteq> Q"
proof -
  have 1: "P = TRR1(RR P)" "Q = TRR1(RR Q)" 
    by (simp_all add: Healthy_if TRR_TRR1 TRR_implies_RR assms(1-2))
  have "(\<And> t s s' r p. U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> TRR1(RR P)) 
                     \<sqsubseteq> U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> TRR1(RR Q)))"
    using assms(3)
    apply(subst (asm) 1(1))
    apply(subst (asm) 1(2))
    by simp
  hence "TRR1(RR P) \<sqsubseteq> TRR1(RR Q)"
    by (rel_auto)
  thus ?thesis
    using "1"(1) "1"(2) by fastforce
qed

lemma TRR_transfer_eq:
  fixes P Q :: "('s, 'e) taction"
  assumes "P is TRR" "Q is TRR" 
    "(\<And> t s s' r p. U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> P) 
                   = U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> Q))"
  shows "P = Q"
proof -
  have 1: "P = TRR1(RR P)" "Q = TRR1(RR Q)" 
    by (simp_all add: Healthy_if TRR_TRR1 TRR_implies_RR assms(1-2))
  have "(\<And> t s s' r p. U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> TRR1(RR P)) 
                     = U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> TRR1(RR Q)))"
    using assms(3)
    apply(subst (asm) 1(1))
    apply(subst (asm) 1(2))
    by simp
  hence "TRR1(RR P) = TRR1(RR Q)"
    by (rel_auto)
  thus ?thesis
    using "1"(1) "1"(2) by fastforce
qed

lemmas TRR_transfer = TRR_transfer_refine TRR_transfer_eq

text \<open> Tailored proof strategy -- eliminates irrelevant variables like ok, wait, tr and ref. \<close>

method trr_simp uses cls = (rule_tac TRR_transfer, simp add: closure cls, simp add: closure cls, rel_simp)

method trr_auto uses cls = (rule_tac TRR_transfer, simp add: closure cls, simp add: closure cls, rel_auto)

lemma TRRw_closed_disj [closure]:
  assumes "P is TRRw" "Q is TRRw"
  shows "(P \<or> Q) is TRRw"
  by (simp add: TRRw_Continuous TRRw_idem assms(1) assms(2) utp_theory.intro
      utp_theory_continuous.disj_is_healthy utp_theory_continuous.intro
      utp_theory_continuous_axioms.intro)

lemma TRR_closed_disj [closure]:
  assumes "P is TRR" "Q is TRR"
  shows "(P \<or> Q) is TRR"
  by (simp add: TRR_Continuous TRR_idem assms(1) assms(2) utp_theory.intro
      utp_theory_continuous.disj_is_healthy utp_theory_continuous.intro
      utp_theory_continuous_axioms.intro)

(*
(*  :: "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" *)
definition t_not ("\<not>\<^sub>t _" [40] 40) 
where [upred_defs]: "(\<not>\<^sub>t P) = U(TRR6(\<not>\<^sub>r P))"

no_utp_lift t_not

(* :: "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" *)
definition t_diff (infixl "-\<^sub>r" 65)
where [upred_defs]: "t_diff P Q = (P \<and> \<not>\<^sub>r Q)"

(*  "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" *) 

definition rea_impl (infixr "\<Rightarrow>\<^sub>t" 25)
where [upred_defs]: "(P \<Rightarrow>\<^sub>t Q) = (\<not>\<^sub>t P \<or> Q)"

lemma TRR_closed_neg [closure]: "\<not>\<^sub>t P is TRR6"
  by (rel_auto)
*)

lemma TRRw_closed_neg [closure]:
  assumes "P is TRRw"
  shows "\<not>\<^sub>r P is TRRw"
proof -
  have "\<not>\<^sub>r TRRw(P) is TRRw"
    by (rel_auto)
  thus "?thesis"
    by (simp add: Healthy_if assms)
qed

(*
lemma TRR_closed_neg [closure]:
  assumes "P is TRR1" "P is RR"
  shows "\<not>\<^sub>r P is TRR1"
  apply(rule TRR1_intro)
  using assms(1) apply(rel_simp)
  apply(simp add: unrest assms)
*)
(*
lemma TRR_closed_neg [closure]: "P is TRR \<Longrightarrow> \<not>\<^sub>t P is TRR"
  apply(rule TRR_intro)
  apply(rel_auto)
  by (rule TRR_intro, simp_all add: unrest closure)

lemma TRR_closed_impl [closure]:
  assumes "P is TRR" "Q is TRR"
  shows "(P \<Rightarrow>\<^sub>r Q) is TRR"
  by (simp add: TRR_closed_disj TRR_closed_neg assms(1) assms(2) rea_impl_def)
*)

lemma TRR_conj [closure]:
  assumes "P is TRR" "Q is TRR"
  shows "P \<and> Q is TRR"
proof -
  have "TRR(P) \<and> TRR(Q) is TRR"
    unfolding Healthy_def by (rrel_auto cls: assms)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRR_ex_ref' [closure]:
  assumes "P is TRR"
  shows "(\<exists> $ref\<acute> \<bullet> P) is TRR"
proof -
  have "(\<exists> $ref\<acute> \<bullet> TRR(P)) is TRR"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed


lemma TRR_ex_pat' [closure]:
  assumes "P is TRR"
  shows "(\<exists> $pat\<acute> \<bullet> P) is TRR"
proof -
  have "(\<exists> $pat\<acute> \<bullet> TRR(P)) is TRR"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRR6_not_refines:
  "(P is TRR6) \<Longrightarrow> ((\<not>\<^sub>r P) \<sqsubseteq> (\<not>\<^sub>r P)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>)"
proof -
  assume 1: "P is TRR6"
  have "(\<not>\<^sub>r TRR6(P)) \<sqsubseteq> (\<not>\<^sub>r TRR6(P))\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>"
    by (rel_auto)
  thus "(\<not>\<^sub>r P) \<sqsubseteq> (\<not>\<^sub>r P)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>"
    by (simp add: Healthy_if 1)
qed

lemma not_refines_TRR6:
  "P is R1 \<Longrightarrow> ((\<not>\<^sub>r P) \<sqsubseteq> (\<not>\<^sub>r P)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>) \<Longrightarrow> (P is TRR6)"
proof -
  assume 1: "P is R1"
  assume "(\<not>\<^sub>r P) \<sqsubseteq> (\<not>\<^sub>r P)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>"
  hence "R1(P) is TRR6"
    by (rel_auto; smt (z3))
  thus "P is TRR6"
    by (simp add: "1" Healthy_if)
qed

lemma TRR_USUP_closed [closure]:
  assumes "\<And> i. P(i) is TRR" "I \<noteq> {}"
  shows "(\<And> i\<in>I \<bullet> P(i)) is TRR"
proof -
  have "\<And> i. (\<not>\<^sub>r P(i)) \<sqsubseteq> ((\<not>\<^sub>r P(i))\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>)"
    by (metis Healthy_if Healthy_intro TRR6_idem TRR6_not_refines TRR_def assms(1))
  hence "(\<Or> i\<in>I \<bullet> \<not>\<^sub>r P(i)) \<sqsubseteq> (\<Or> i\<in>I \<bullet> ((\<not>\<^sub>r P(i))\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>))"
    by (rel_blast)
  hence "\<not>\<^sub>r (\<Or> i\<in>I \<bullet> \<not>\<^sub>r P(i)) is TRR6"
    by (simp add: UINF_R1_closed not_refines_TRR6 rea_not_R1 rea_not_not subst_UINF)
  moreover have "\<not>\<^sub>r (\<Or> i\<in>I \<bullet> \<not>\<^sub>r P(i)) is TRRw"
    by (meson TRR_TRRw TRRw_Continuous TRRw_closed_neg UINF_mem_Continuous_closed assms)
  moreover have "(\<And> i\<in>I \<bullet> P(i)) = (\<not>\<^sub>r (\<Or> i\<in>I \<bullet> \<not>\<^sub>r P(i)))"
    by (simp add: rpred closure assms)
  ultimately show ?thesis
    by (simp add: Healthy_def TRR_def)
qed

lemma TRRw_closed_wp [closure]: "\<lbrakk> P is TRRw; Q is TRRw \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is TRRw"
  by (simp add: wp_rea_def closure)


lemma TRR6_closed_wp [closure]: "Q is TRR6 \<Longrightarrow> P wp\<^sub>r Q is TRR6"
proof -
  assume "Q is TRR6"
  hence "(\<not>\<^sub>r Q) \<sqsubseteq> (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>"
    by (meson TRR6_not_refines)
  hence "(P ;; (\<not>\<^sub>r Q)) \<sqsubseteq> (P ;; (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>)"
    by (meson urel_dioid.mult_isol)
  moreover have "(P ;; (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>) = (P ;; (\<not>\<^sub>r Q))\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>"
    by rel_auto
  ultimately have "(P ;; (\<not>\<^sub>r Q)) \<sqsubseteq> (P ;; (\<not>\<^sub>r Q))\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>"
    by simp
  hence "\<not>\<^sub>r (P ;; (\<not>\<^sub>r Q)) is TRR6"
    by (smt (verit) R1_rea_not R1_rea_not' TRR6_equiv TRR6_not_refines disj_upred_def not_refines_TRR6 out_var_semi_uvar pat_vwb_lens rea_not_R1 rea_not_def semilattice_sup_class.sup.order_iff subst_disj subst_not unrest_as_subst unrest_lit unrest_usubst_single utp_pred_laws.compl_le_compl_iff vwb_lens_mwb)
  thus ?thesis
    by (simp add: wp_rea_def)
qed

lemma TRR_closed_wp [closure]: "\<lbrakk> P is TRR; Q is TRR \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is TRR"
  by (metis Healthy_if Healthy_intro TRR6_closed_wp TRR_TRRw TRR_def TRRw_closed_wp)

lemma TRR_RC2_closed [closure]:
   assumes "P is TRR" shows "RC2(P) is TRR"
proof -
  have "RC2(TRR(P)) is TRR"
    by (rel_auto)
       (metis (no_types, hide_lams) Prefix_Order.prefixE Prefix_Order.prefixI append.assoc plus_list_def trace_class.add_diff_cancel_left)+
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRR_left_unit [rpred]: 
  assumes "P is TRR"
  shows "II\<^sub>t ;; P = P"
  by (metis Healthy_if TRR1_def TRR_TRR1 assms)

method rrel_simp uses cls = (rule RR_eq_transfer, simp add: closure cls, simp add: closure cls)

lemma TRR_ident_intro:
  assumes "P is RR" "P is TRR6" "II\<^sub>t ;; P = P"
  shows "P is TRR"
  by (simp add: Healthy_if Healthy_intro TRR1_def TRR_def TRRw_def assms(1) assms(2) assms(3))

lemma TRR_wp_closure [closure]:
  assumes "P is TRR" "Q is TRC"
  shows "P wp\<^sub>r Q is TRC"
  by (metis Healthy_def TRC_def TRC_implies_RC TRC_implies_TRR TRR1_def TRR_closed_wp TRR_implies_RR TRR_left_unit assms(1) assms(2) wp_rea_RC)

lemma TRR_wp_unit [wp]:
  assumes "P is TRC"
  shows "II\<^sub>t wp\<^sub>r P = P"
proof -
  have "II\<^sub>t wp\<^sub>r (TRC P) = TRC P"
    by (trr_auto cls: assms)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRC_wp_intro:
  assumes "P is RC" "II\<^sub>t wp\<^sub>r P = P"
  shows "P is TRC"
proof -
  have "II\<^sub>t wp\<^sub>r (RC2 (RR P)) is TRC"
    apply (rel_auto)
    apply (metis (no_types, hide_lams) Prefix_Order.prefixE Prefix_Order.prefixI Prefix_Order.same_prefix_prefix order_refl plus_list_def trace_class.add_diff_cancel_left)
    apply (meson minus_cancel_le order.trans)
    done
  thus ?thesis
    by (simp add: Healthy_if RC_implies_RR RC_prefix_closed assms)
qed

lemma TRC_rea_true [closure]: "true\<^sub>r is TRC" by rel_auto

interpretation trel_theory: utp_theory_continuous TRR
  rewrites "P \<in> carrier trel_theory.thy_order \<longleftrightarrow> P is TRR"
  and "le trel_theory.thy_order = (\<sqsubseteq>)"
  and "eq trel_theory.thy_order = (=)"  
  and trel_top: "trel_theory.utp_top = false"
  and trel_bottom: "trel_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous TRR
    by (unfold_locales, simp_all add: TRR_idem TRR_Continuous)
  show top:"utp_top = false"          
    by (simp add: healthy_top, rel_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, rel_auto)
  show "utp_theory_continuous TRR"
    by (unfold_locales, simp_all add: closure rpred top)
qed (simp_all)

interpretation tfin_theory: utp_theory_continuous TRF
  rewrites "P \<in> carrier tfin_theory.thy_order \<longleftrightarrow> P is TRF"
  and "le tfin_theory.thy_order = (\<sqsubseteq>)"
  and "eq tfin_theory.thy_order = (=)"  
  and tfin_top: "tfin_theory.utp_top = false"
  and tfin_bottom: "tfin_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous TRF
    by (unfold_locales, simp_all add: TRF_idem TRF_Continuous)
  show top:"utp_top = false"
    by (simp add: healthy_top, rel_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, rel_auto)
  show "utp_theory_continuous TRF"
    by (unfold_locales, simp_all add: closure rpred top)
qed (simp_all)

text \<open> The following healthiness condition is a weakened form of prefix closure -- a relation must
  admit every idle prefix with the state unchanged and the unstable refusal. \<close>

definition TIP :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TIP(P) = (P \<or> U((\<exists> $st\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> \<exists> t. P\<lbrakk>[],\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> = $tr @ idleprefix(\<guillemotleft>t\<guillemotright>)) \<and> $st\<acute> = $st \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute>))"

utp_const RR TIP

lemma TIP_idem [simp]: "TIP (TIP P) = TIP P"
  by (rel_auto, blast)

lemma TIP_prop:
  assumes "P is TRR" "P is TIP"
  shows "U(P\<lbrakk>$st,\<^bold>\<bullet>,True,[],idleprefix($tr\<acute>-$tr)/$st\<acute>,$ref\<acute>,$pat\<acute>,$tr,$tr\<acute>\<rbrakk>) \<sqsubseteq> P" 
proof -
  have "U(TIP(TRR(P))\<lbrakk>$st,\<^bold>\<bullet>,True,[],idleprefix($tr\<acute>-$tr)/$st\<acute>,$ref\<acute>,$pat\<acute>,$tr,$tr\<acute>\<rbrakk>) \<sqsubseteq> TRR(P)"
    by (rel_auto; metis)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRR_TIP_closed [closure]:
  assumes "P is TRR"
  shows "TIP(P) is TRR"
proof -
  have "TIP(TRR(P)) is TRR"
    by (rel_auto; fastforce)
  thus ?thesis by (simp add: Healthy_if assms)
qed

no_utp_lift lift_state_rel

definition TDC :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[upred_defs]: "TDC(P) = U(\<exists> ref\<^sub>0. P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<le> \<guillemotleft>ref\<^sub>0\<guillemotright>)"

lemma TRC_unrests:
  assumes "P is TRC"
  shows "$ref \<sharp> TRC(P)" "$ref\<acute> \<sharp> TRC(P)"
        "$pat \<sharp> TRC(P)" "$pat\<acute> \<sharp> TRC(P)"        
        "$ok \<sharp> TRC(P)" "$ok\<acute> \<sharp> TRC(P)"
        "$wait \<sharp> TRC(P)" "$wait\<acute> \<sharp> TRC(P)"
  by (rel_auto+)

lemma TRC_unrests':
  assumes "P is TRC"
  shows "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$pat \<sharp> P" "$pat\<acute> \<sharp> P"
        "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  by (metis Healthy_if TRC_unrests assms)+

subsection \<open> Concretification laws \<close>

lemma TRRUnrestConcretify:
  assumes "$ref \<sharp> P" "$pat \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>False\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$ref,$pat\<rbrakk>)"
  using assms by pred_auto

lemma TRFUnrestConcretify:
  assumes "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>False\<guillemotright>,\<guillemotleft>False\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$ref,$ref\<acute>,$pat,$pat\<acute>\<rbrakk>)"
  using assms by pred_auto

lemma TRCconcretify:
  assumes "P is TRC"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>False\<guillemotright>,\<guillemotleft>False\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$ref,$ref\<acute>,$pat,$pat\<acute>\<rbrakk>)"
  by (rule TRFUnrestConcretify)
     (simp_all add: TRC_unrests' assms)

lemma TRRwconcretify:
  assumes "P is TRRw"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>False\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$ref,$pat\<rbrakk>)"
proof -
  have "$ref \<sharp> P" "$pat \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" 
    by (simp_all add: assms closure unrest)
  thus ?thesis
    by (rule TRRUnrestConcretify)
qed

lemma TRRconcretify:
  assumes "P is TRR"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>False\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$ref,$pat\<rbrakk>)"
  by (meson TRR_TRRw TRRwconcretify assms)

lemma TRFconcretify:
  assumes "P is TRF"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>, \<guillemotleft>False\<guillemotright>,\<guillemotleft>False\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$ref,$ref\<acute>,$pat,$pat\<acute>\<rbrakk>)"
proof -
  have "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$pat \<sharp> P" "$pat\<acute> \<sharp> P"  "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRF_implies_TRR TRR_implies_RR assms)
  thus ?thesis
    by (rule TRFUnrestConcretify)
qed                    

end