section \<open> Simple UTP real-time theory \<close>

theory utp_simple_time imports "UTP.utp" begin
  
alphabet 's st_time = 
  time :: nat  st :: 's
  
type_synonym 's time_rel = "'s st_time hrel"

definition HT :: "'s time_rel \<Rightarrow> 's time_rel" where
[upred_defs]: "HT(P) = (P \<and> $time \<le>\<^sub>u $time\<acute>)"

definition Wait :: "nat \<Rightarrow> 's time_rel" where
[upred_defs]: "Wait(n) = ($time\<acute> =\<^sub>u $time + \<guillemotleft>n\<guillemotright> \<and> $st\<acute> =\<^sub>u $st)"

theorem HT_idem: "HT(HT(P)) = HT(P)" by rel_auto

theorem HT_mono: "P \<sqsubseteq> Q \<Longrightarrow> HT(P) \<sqsubseteq> HT(Q)" by rel_auto

lemma HT_Wait: "HT(Wait(n)) = Wait(n)" by (rel_auto)

lemma HT_Wait_closed [closure]: "Wait(n) is HT"
  by (simp add: HT_Wait Healthy_def)

lemma HT_skip_closed [closure]: "II is HT"
  by (rel_auto)

lemma HT_seqr_closed [closure]:
  "\<lbrakk> P is HT; Q is HT \<rbrakk> \<Longrightarrow> P ;; Q is HT"
  by (rel_auto, meson dual_order.trans) \<comment> \<open> Sledgehammer required \<close>
    
theorem Wait_skip: "Wait(0) = II" by (rel_auto)
    
theorem Wait_Wait: "Wait(m) ;; Wait(n) = Wait (m + n)" by (rel_auto)
    
end