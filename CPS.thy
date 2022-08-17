theory CPS
  imports Main
begin

datatype 'a category = 
  Atomic 'a ("^")
  | RightFunctional "'a category" "'a category" (infix "→" 60)
  | LeftFunctional "'a category" "'a category" (infix "←" 60) 

inductive  LC:: "'a category list ⇒ 'a category ⇒ bool" (infix "⊢" 55)
  where
    r1: "([x]⊢x)"
  | r2: "(X@[x]⊢y) ⟹ (X⊢y←x)"
  | r3: "([x]@X⊢y) ⟹ (X⊢x→y)"
  | r4: "⟦(Y⊢y); (X@[x]@Z⊢z)⟧ ⟹ (X@Y@[y→x]@Z⊢z)"
  | r5: "⟦(X@[x]@Z⊢z); (Y⊢y)⟧ ⟹ (X@[x←y]@Y@Z⊢z)"

theorem
  assumes "distinct [a,b,c,d]"
  shows "¬([^a←^b,^a→^c]⊢^c←^b)"
proof -
have p9: "¬([]⊢^b)"
  apply auto apply (subst (asm) LC.simps) by auto
have p6: "¬([^a← ^b]⊢^a)"
  apply auto apply (subst (asm) LC.simps) apply auto 
  by  (simp add: p9 Cons_eq_append_conv)+ 
have p10: "¬([]⊢^a)"
  apply auto apply (subst (asm) LC.simps) by auto
have p15: "¬([^c,^b]⊢^c)"
  apply auto apply (subst (asm) LC.simps) apply auto
  by (simp add: p10 Cons_eq_append_conv)+
have p12: "¬([^a,^a→ ^c,^b]⊢^c)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p10 p15 by fastforce
have p16: "¬([^a,^b]⊢^c)"
  apply auto apply (subst (asm) LC.simps) apply auto
  by (simp_all add: Cons_eq_append_conv)+
have p17: "¬([^a]⊢^c)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using assms by auto
have p4: "¬([^a← ^b,^a→ ^c,^b]⊢^c)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p10 p15 p12 p16 p17 by fastforce+
have p23: "¬([^c]⊢^c← ^b)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  by (simp add: p15)
have p19: "¬([^a,^a→ ^c]⊢^c← ^b)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p10 p23 p12 by auto+  
have p25: "¬([^a]⊢^c← ^b)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  by (simp add: p16) 
show p2: "¬([^a← ^b,^a→ ^c]⊢^c← ^b)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p10 p23 p4 p25 p9 by fastforce+
qed

lemma
  assumes "distinct [a,b,c,d]"
  shows "¬(
    [^a←(^b←^c)] ⊢^d←(((^d←(^a→^d))←((^d←(^b→^d))←^c))→^d)
  )"
proof -
have p17: "¬([^a,^d]⊢^a)"
  apply auto apply(subst (asm) LC.simps) apply auto
  by (simp add: Cons_eq_append_conv)+
have p16: "¬([^a,^d←(^b→^d)]⊢^a)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p17 by fastforce+
have p14: "¬([^a,(^d←(^b→^d))←^c]⊢^a)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p16 by fastforce+
have p26: "¬([^d,^c]⊢^b)"
  apply auto apply(subst (asm) LC.simps) apply auto
  by (simp add: Cons_eq_append_conv)+
have p27: "¬([^d]⊢^b)"
  apply auto apply(subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using assms by auto
have p25: "¬([^d←(^b→^d),^c]⊢^b)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p26 p27 by fastforce+
have p29: "¬([^d←(^b→^d)]⊢^b)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p27 by fastforce+
have p23: "¬([(^d←(^b→^d))←^c,^c]⊢^b)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p25 p29 by fastforce+
have p33: "¬([^d]⊢^b←^c)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p26 by fastforce+
have p31: "¬([^d←(^b→^d)]⊢^b←^c)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p25 p33 by fastforce+
have p21: "¬([(^d←(^b→^d))←^c]⊢^b←^c)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p23 p31 by fastforce+
have p39: "¬([^a←(^b←^c),^d]⊢^a)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p17 p33 by fastforce+
have p35: "¬([^a←(^b←^c),^d←(^b→^d)]⊢^a)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p16 p31 p39 by fastforce+
have p12: "¬([^a←(^b←^c),(^d←(^b→^d))←^c]⊢^a)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p14 p21 p35 by fastforce+
have p46: "¬([^d]⊢^a)"
  apply auto apply(subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using assms by auto
have p45: "¬([^d←(^b→^d)]⊢^a)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p46 by fastforce+
have p43: "¬([(^d←(^b→^d))←^c]⊢^a)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p45 by fastforce+
have p47: "¬([]⊢^a)"
  apply auto apply (subst (asm) LC.simps) by auto
have p53: "¬([^a,^d,^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p17 p46 p47 by fastforce+
have p54: "¬([^a,^d]⊢^d)"
  apply auto apply(subst (asm) LC.simps) apply auto
  by (simp add: Cons_eq_append_conv)+
have p51: "¬([^a,^d←(^b→^d),^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p16 p45 p47 p53 p54 by fastforce+
have p56: "¬([^a,^d←(^b→^d)]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p54 by fastforce+
have p49: "¬([^a,(^d←(^b→^d))←^c,^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p14 p43 p47 p51 p56 by fastforce+
have p63: "¬([^a]⊢^d)"
  apply auto apply(subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using assms by auto
have p73: "¬([^a←(^b←^c),^d,^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p39 p46 p47 p53 p33 p63 by fastforce+
have p81: "¬([^a←(^b←^c),^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p54 p63 by fastforce+
have p65: "¬([^a←(^b←^c),^d←(^b→^d),^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p35 p45 p47 p51 p31 p63 p73 p81 by fastforce+
have p83: "¬([^a←(^b←^c),^d←(^b→^d)]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p56 p63 p81 by fastforce+
have p10: "¬([^a←(^b←^c),(^d←(^b→^d))←^c,^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p12 p43 p47 p49 p21 p63 p65 p83 by fastforce+
have p89: "¬([^a,^d]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p53 by fastforce+
have p87: "¬([^a,^d←(^b→^d)]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p51 p89 by fastforce+
have p85: "¬([^a,(^d←(^b→^d))←^c]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p49 p87 by fastforce+
have p109: "¬([^a←(^b←^c),^d]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p73 p89 p33 by fastforce+
have p99: "¬([^a←(^b←^c),^d←(^b→^d)]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p65 p87 p31 p109 by fastforce+
have p8: "¬([^a←(^b←^c),(^d←(^b→^d))←^c]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p10 p85 p21 p99 by fastforce+
have p119: "¬([^a]⊢(^d←(^a→^d))←((^d←(^b→^d))←^c))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p85 by fastforce+
have p6: "¬([^a←(^b←^c)]⊢(^d←(^a→^d))←((^d←(^b→^d))←^c))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p8 p119 by fastforce+
have p129: "¬([^d,^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p46 p47 by fastforce+
have p136: "¬([^b]⊢^a)"
  apply auto apply(subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using assms by auto
have p135: "¬([^b,^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p136 p47 by fastforce+
have p133: "¬([^a→^d]⊢^b→^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using r1 p136 p135 p47 by fastforce+
have p127: "¬([^d←(^b→^d),^a→^d]⊢^d)"  
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p45 p47 p129 p133 by fastforce+
have p143: "¬([^b]⊢^d)"
  apply auto apply(subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using assms by auto
have p142: "¬([]⊢^b→^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  using p143 by fastforce+
have p138: "¬([^d←(^b→^d)]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p142 by fastforce+
have p125: "¬([(^d←(^b→^d))←^c,^a→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p43 p47 p127 p138 by fastforce+
have p147: "¬([^d]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p129 by fastforce+
have p145: "¬([^d←(^b→^d)]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using r1 p136 p127 p147 by fastforce+
have p123: "¬([(^d←(^b→^d))←^c]⊢^d←(^a→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p125 p145 by fastforce+
have p121: "¬([]⊢(^d←(^a→^d))←((^d←(^b→^d))←^c))"
  apply auto apply (subst (asm) LC.simps) apply auto
  using p123 by fastforce+
have p149: "¬([^a,((^d←(^a→^d))←((^d←(^b→^d))←^c))→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p119 p121 by fastforce+
have p4: 
  "¬([^a←(^b←^c),((^d←(^a→^d))←((^d←(^b→^d))←^c))→^d]⊢^d)"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p6 p121 p149 p63 by fastforce+
have p151:
  "¬([^a]⊢^d←(((^d←(^a→^d))←((^d←(^b→^d))←^c))→^d))"
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p149 by fastforce+
show p2: ?thesis
  apply auto apply (subst (asm) LC.simps) apply auto
  apply (simp_all add: Cons_eq_append_conv)+
  using p4 p151 by fastforce+
qed
end