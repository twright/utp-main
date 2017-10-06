theory Modelica_Blocks_Core
  imports "../Modelica_Core"
begin
  
consts
  eps\<^sub>m :: real
  
type_synonym ('a, 'c) mcon = "('a \<Longrightarrow> 'c mst_scheme)"
  
translations
  (type) "('a, 'c) mcon" <= (type) "('a \<Longrightarrow> 'c mst_scheme)"
  
datatype 'c mevgrd =
  TimeEvent (ofTimeEvent: "real \<Rightarrow> bool") | StateEvent (ofStateEvent: "(real, 'c) mexpr")
  
print_theorems
  
record (overloaded) 'c mblock = 
  minit :: "'c mst_scheme upred"
  mceqs :: "'c mrel"
  mgrds :: "('c mevgrd \<times> 'c mrel) list"
  
definition timeGuards :: "'c mblock \<Rightarrow> ((real \<Rightarrow> bool) \<times> 'c mrel) list" where
[upred_defs, mo_defs]:
"timeGuards M = map (\<lambda> (g, e). (ofTimeEvent g, e)) (filter (is_TimeEvent \<circ> fst) (mgrds M))"

definition stateGuards :: "'c mblock \<Rightarrow> ((real, 'c) mexpr \<times> 'c mrel) list" where
[upred_defs, mo_defs]:
"stateGuards M = map (\<lambda> (g, e). (ofStateEvent g, e)) (filter (Not \<circ> is_TimeEvent \<circ> fst) (mgrds M))"

text {* A time event is triggered whenever the internal clock hits one of the instants in
  the given set of real number. *}
  
definition ti_event :: "(real \<Rightarrow> bool) \<Rightarrow> 'c mst_scheme hrel" where
[upred_defs, mo_defs]: "ti_event P = (\<guillemotleft>P\<guillemotright>($time\<acute>)\<^sub>a)"
  
text {* State events are recorded whenever the given function crosses zero. A zero crossing event 
  is registered at some non-deterministically chosen instant when the function $zcf$ was previously 
  $\ge eps$ and it becomes less than $eps$. There is not one point which satisifies this specification 
  and then event can occur at any $t$ when $zcf(t) \in [0,eps)$ *}
  
definition zc_event :: "(real, 'c mst_scheme) uexpr \<Rightarrow> 'c mst_scheme hrel \<times> 'c mst_scheme hrel" where
[upred_defs, mo_defs]: "zc_event zcf = (\<lceil>zcf\<rceil>\<^sub>> \<ge>\<^sub>u 0, (\<lceil>zcf \<ge>\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>\<rceil>\<^sub>< \<and> \<lceil>zcf <\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>\<rceil>\<^sub>>))"
  
text {* When the zero-crossing function was previously close to 0, but now it is sufficiently far
  away ($> eps$), a "phantom" event iteration executes which simply resets the previous value
  of the zero crossing function to that point so that any correspondonding when statement is
  re-enabled. *}

definition zc_restore :: "(real, 'c mst_scheme) uexpr \<Rightarrow> 'c mst_scheme hrel" where
[upred_defs, mo_defs]: "zc_restore zcf = (\<lceil>zcf <\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>\<rceil>\<^sub><  \<and> \<lceil>zcf \<ge>\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>\<rceil>\<^sub>>)"

definition minvs :: "'c mblock \<Rightarrow> 'c mst_scheme hrel" where
[upred_defs, mo_defs]: 
  "minvs M = foldr (op \<and>) (map (fst \<circ> zc_event \<circ> fst) (stateGuards M)) true"

definition mconds :: "'c mblock \<Rightarrow> 'c mst_scheme hrel" where
[upred_defs, mo_defs]: 
  "mconds M = (foldr (op \<or>) (map (snd \<circ> zc_event \<circ> fst) (stateGuards M)) false \<or>
               foldr (op \<or>) (map (zc_restore \<circ> fst) (stateGuards M)) false \<or> 
               foldr (op \<or>) (map (ti_event \<circ> fst) (timeGuards M)) false)"
  
text {* For discrete events, we first execute each time event up to once, and then enter iteration
  for the state events. *}
  
definition mdeqs :: "('c::t2_space) mblock \<Rightarrow> 'c mrel" where
[upred_defs, mo_defs]: "mdeqs M = 
   (foldr (op ;;) (map (\<lambda> (R, dq). dq \<triangleleft> \<guillemotleft>R\<guillemotright>(&\<^bold>c:time)\<^sub>a \<triangleright>\<^sub>R II\<^sub>R) (timeGuards M)) II\<^sub>R) ;;
   (\<mu>\<^sub>R X \<bullet> foldr 
           (\<lambda> (zcf, dq) q. 
           (dq ;; X) \<triangleleft> (\<lceil>zcf\<rceil>\<^sub>< \<ge>\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>)\<lbrakk>&\<^bold>d/&\<^bold>c\<rbrakk> \<and> (\<lceil>zcf\<rceil>\<^sub>< <\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>) \<triangleright>\<^sub>R q) (stateGuards M) II\<^sub>R)"
 (* zcf  previously not satisfied ---^               ^--- now it is *)

definition CoreTime :: "('c::t2_space) mblock" where
[upred_defs, mo_defs]:
  "CoreTime = \<lparr> minit = (&time =\<^sub>u 0), mceqs = &time \<leftarrow>\<^sub>H ($time + \<guillemotleft>ti\<guillemotright>), mgrds = [] \<rparr>"

definition mblock_comp :: "'c mblock \<Rightarrow> 'c mblock \<Rightarrow> 'c mblock" (infixr "\<oplus>\<^sub>m" 85) where
[upred_defs, mo_defs]:
"A \<oplus>\<^sub>m B = \<lparr> minit = (minit A \<and> minit B)
          , mceqs = (mceqs A \<and> mceqs B)
          , mgrds = (mgrds A @ mgrds B) \<rparr>"
  
definition mblock_sem :: "('c::t2_space) mblock \<Rightarrow> 'c mrel" ("\<lbrakk>_\<rbrakk>\<^sub>m") where
[upred_defs, mo_defs]:
"\<lbrakk>M\<rbrakk>\<^sub>m = (let M' = CoreTime \<oplus>\<^sub>m M in
        \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> [minit M']\<^sub>C\<^sub>>) ;; 
        (\<mu>\<^sub>R X \<bullet> \<^bold>d :=\<^sub>R &\<^bold>c ;; ((mceqs M') [minvs M' | mconds M']\<^sub>H\<^sup>+ (mdeqs M')) ;; X))"
  
default_sort t2_space
end
