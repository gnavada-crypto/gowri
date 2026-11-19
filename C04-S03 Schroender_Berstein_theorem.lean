import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Set
import Mathlib.Tactic.WLOG

open Set
open Function

noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]

section
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_sdiff]
    exact ⟨trivial, hx⟩ 
    
  have : ∃ y, g y = x := by
    rcases this with ⟨ y, hy⟩ 
    use y 
    exact hy.right
  exact invFun_eq this 


  #check invFun_eq
  --#check wlog

theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [ite_eq_left x₁A, ite_eq_right x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        have k: g (f x₁) =g (invFun g x₂):= congrArg g hxeq 
         /- rw[hxeq]
        rw[sb_right_inv f g x₂nA] at k
        exact k.symm-/
            
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    rw [ite_eq_left x₁A, ite_eq_left x₂A] at hxeq
    exact hf hxeq
  · push Not at xA  
    rw [ite_eq_right xA.left, ite_eq_right xA.right] at hxeq
    have l: g (invFun g x₁) = g (invFun g x₂):= by
      rw [hxeq]
    rw[sb_right_inv f g (xA.left), sb_right_inv f g (xA.right)] at l 
    exact l

#check _root_.not_imp_self
#check ite_eq_left

theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    rw [h_def, sbFun, ite_eq_left this]
    apply hg hx

  · use (g y)
    rw [h_def, sbFun, (ite_eq_right gyA)]
    --rw[A_def] at gyA
    have k:g (invFun g (g y))= g y := by
      rw[sb_right_inv f g gyA] 
    exact hg k
end

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h := 
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
