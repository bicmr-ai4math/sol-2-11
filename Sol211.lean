import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Hom.Group
import Mathlib.Data.Set.Function
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
section

structure isExact₁ [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : AddMonoidHom A B) (g : B →+ C) : Prop where
  imsubker : ∀ a : A, g (f a) = 0
  kersubim : ∀ b : B, g b = 0 → ∃ a : A, b = f a

def isComm₁ [AddCommGroup A][AddCommGroup B][AddCommGroup C][AddCommGroup D] (f:A→+B)(g:B→+D)(h:A→+C)(l:C→+D) : Prop := ∀ a :A, g (f a)=l (h a)

lemma fourlemma1 {A1 B1 C1 D1 A2 B2 C2 D2 : Type}[AddCommGroup A1][AddCommGroup B1][AddCommGroup C1][AddCommGroup D1][AddCommGroup A2][AddCommGroup B2][AddCommGroup C2][AddCommGroup D2](f1 : A1 →+ B1)(g1 : B1 →+ C1)(h1 : C1 →+ D1)(f2 : A2 →+ B2)(g2 : B2 →+ C2)(h2 : C2 →+ D2)(α : A1 →+ A2)(β : B1 →+ B2)(γ : C1 →+ C2)(δ : D1 →+ D2)(f1g1:isExact₁ f1 g1)(g1h1:isExact₁ g1 h1)(f2g2:isExact₁ f2 g2)(_g2h2:isExact₁ g2 h2)(Comm1:isComm₁ f1 β α f2)(Comm2:isComm₁ g1 γ β g2)(Comm3:isComm₁ h1 δ γ h2)(sura:Function.Surjective α)(injb:Function.Injective β)(injd:Function.Injective δ) : Function.Injective γ := by
  unfold Function.Injective
  intro a b p1
  have p2: h2 (γ a)=h2 (γ b)
  rw [p1]
  have p3: δ (h1 a) = h2 (γ a)
  apply Comm3
  have p4: δ (h1 b) = h2 (γ b)
  apply Comm3
  have p5: δ (h1 a)=δ (h1 b)
  rw [p3,p4,p2]
  have p6:h1 a=h1 b
  apply injd p5
  have p7: h1 (a-b)=0
  simp
  rw [p6]
  simp
  have p8:∃ c : B1, a-b=g1 c
  apply g1h1.kersubim
  exact p7
  cases' p8 with c p9
  have p10:γ (g1 c)=0
  rw [← p9]
  simp
  rw [p1]
  simp
  have p11:g2 (β c)=0
  rw [← p10]
  symm
  apply Comm2
  have p12:∃ d : A2,β c=f2 d
  apply f2g2.kersubim
  exact p11
  cases' p12 with d p13
  have p14:∃e:A1,α e=d
  apply sura
  cases' p14 with e p15
  have p16:β (f1 e)=f2 (α e)
  apply Comm1
  have p17:β (f1 e)=β c
  rw [p13, ← p15,p16]
  have p18:f1 e=c
  apply injb p17
  have p19:a-b=0
  rw [p9,← p18]
  apply f1g1.imsubker
  have p20:a=(a-b)+b
  simp
  rw [p20,p19,zero_add]

lemma fourlemma2 {A1 B1 C1 D1 A2 B2 C2 D2 : Type}[AddCommGroup A1][AddCommGroup B1][AddCommGroup C1][AddCommGroup D1][AddCommGroup A2][AddCommGroup B2][AddCommGroup C2][AddCommGroup D2](f1 : A1 →+ B1)(g1 : B1 →+ C1)(h1 : C1 →+ D1)(f2 : A2 →+ B2)(g2 : B2 →+ C2)(h2 : C2 →+ D2)(α : A1 →+ A2)(β : B1 →+ B2)(γ : C1 →+ C2)(δ : D1 →+ D2)(_f1g1:isExact₁ f1 g1)(g1h1:isExact₁ g1 h1)(f2g2:isExact₁ f2 g2)(g2h2:isExact₁ g2 h2)(Comm1:isComm₁ f1 β α f2)(Comm2:isComm₁ g1 γ β g2)(Comm3:isComm₁ h1 δ γ h2)(injd:Function.Injective δ)(sura:Function.Surjective α)(surc:Function.Surjective γ): Function.Surjective β := by
  unfold Function.Surjective
  intro b
  have p1:∃ c:C1,γ c=g2 b
  apply surc
  cases' p1 with c p2
  have p3:δ (h1 c)=h2 (γ c)
  apply Comm3
  have p4:h1 c=0
  apply injd
  rw [p3,p2]
  simp
  apply g2h2.imsubker
  have p5:∃ d:B1,c=g1 d
  apply g1h1.kersubim
  exact p4
  cases' p5 with d p6
  have p7: γ (g1 d)=g2 (β d)
  apply Comm2
  have p8: g2 b=g2 (β d)
  rw [← p7,← p6,p2]
  have p9: g2 (b-β d)=0
  simp
  rw [p8]
  simp
  have p10:∃ e:A2,b-β d=f2 e
  apply f2g2.kersubim
  exact p9
  cases' p10 with e p11
  have p12:∃ s:A1,α s=e
  apply sura
  cases' p12 with s p13
  have p14:β (f1 s)=f2 (α s)
  apply Comm1
  use d+f1 s
  simp
  rw [p14,p13,← p11]
  simp
