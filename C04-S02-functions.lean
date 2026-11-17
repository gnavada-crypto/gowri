
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro fsx x sx
    have h: f x ∈  f '' s := by
      exact mem_image_of_mem f  sx
    --simp
    exact  fsx h
  · intro sfv
    simp [sfv]



#check subset_trans
#check mem_image_of_mem
#check subset_def
#check Injective

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x h₁
  simp at h₁
  rcases h₁ with ⟨y, h₁y⟩
  have h₂: y = x := by
    exact h  h₁y.right
  have h₃:y∈ s := h₁y.left
  rw[h₂] at h₃
  exact h₃



example : f '' (f ⁻¹' u) ⊆ u := by
  intro x h
  simp at h
  rcases h with ⟨ y,  hy⟩
  have h₁: f y ∈ u:=hy.left
  rw[hy.right] at h₁
  exact h₁

/-Shorter proof suggested by google AI
example : f '' (f ⁻¹' u) ⊆ u := by
  intro x h
  rcases h with ⟨ y,  hy, rfl⟩
  exact hy
 -/

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x xu
  simp
  have h₁: ∃ y, f y = x := h x
  rcases h₁ with ⟨y, h₁y⟩
  use y
  constructor
  · rw[← h₁y] at xu
    exact xu
  · exact h₁y




example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y hy
  simp at hy
  rcases hy with ⟨x, hyx⟩
  have h₁: x∈ s:= hyx.left
  simp
  have h₂: x∈ t:= by
    exact h h₁
  use x
  exact ⟨h₂,  hyx.right⟩

/- Easier, shorter proofs:
  example (h : s ⊆ t) : f '' s ⊆ f '' t := by
    intro y hy
    rcases hy with ⟨x, hxs, rfl⟩
    exact ⟨x, h hxs, rfl⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
  fun _ ⟨x, hxs, hxy⟩ => ⟨x, h hxs, hxy⟩

  example (h : s ⊆ t) : f '' s ⊆ f '' t := by
    rintro _ ⟨x, hxs, rfl⟩
    exact ⟨x, h hxs, rfl⟩
-/

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro y hy
  simp at hy
  have h₁: f y ∈ v:= by
    exact h hy
  simp
  exact h₁


example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  rfl

/-Both the LHS and RHS are definitionally same so it needs no proof. If I say constructor, even then the proof closes.-/


example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y hy
  simp at hy
  rcases hy with ⟨ x, hyx, rfl⟩
  constructor
  · simp
    have h₁:x∈ s:= hyx.left
    use x
  · simp
    have h₁:x∈ t:= hyx.right
    use x

/- Shorter proof:
example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y hy
  rcases hy with ⟨x, ⟨hxs, hxt⟩, rfl⟩
  constructor
  · exact ⟨x, hxs, rfl⟩
  · exact ⟨x, hxt, rfl⟩
-/


example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨ hy1, hy2⟩
  simp at hy1 hy2
  rcases hy1 with ⟨ x1, ⟨xs, hy1x1⟩⟩
  rcases hy2 with ⟨ x2, ⟨xt, rfl⟩⟩
  have h₁:  x1 = x2:= h hy1x1
  have h₂:x2∈ s∩ t:= by
    rw[h₁] at xs
    exact ⟨xs, xt⟩
  use x2

/-Earlier I qrote
rcases hy2 with ⟨ x2, ⟨xt, hy2x2, rfl⟩⟩
in place of
rcases hy2 with ⟨ x2, ⟨xt, rfl⟩⟩
But hy2x2 disappeared because it becomes exactly same as hy1x1
 -/

--#check

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y hy
  simp at hy
  rcases hy with ⟨h1, h2⟩
  rcases h1 with⟨x, h3, h4⟩
  simp
  have h5: x∉ t:= by
    by_contra h6
    specialize h2 x
    exact h2 h6 h4
  use x

  /- A shorted proof using lambda function:

  example : f '' s \ f '' t ⊆ f '' (s \ t) := by
    rintro y ⟨⟨x, xs, rfl⟩, h2⟩
    refine ⟨x, ⟨xs, fun xt => h2 ⟨x, xt, rfl⟩⟩, rfl⟩
  -/




example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x hx
  simp at hx
  simp
  exact hx

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  have h1: f '' f ⁻¹' v ⊆ v:= image_preimage_subset f v
  have h2: f '' (s ∩ f ⁻¹' v) ⊆ f '' s  ∩ f '' ( f ⁻¹' v) := image_inter_subset f s (f ⁻¹' v)
  have h4:f '' (s ∩ f ⁻¹' v)⊆ f '' s ∩ v:=  by
    have h5:f '' s ∩  f '' f ⁻¹' v⊆ f '' s ∩ v:=
      fun _x ⟨xs, xv⟩ ↦ ⟨xs, h1 xv⟩
    exact subset_trans h2 h5
  have h6:f '' s ∩ v⊆ f '' (s ∩ f ⁻¹' v) := by
    intro y hy
    simp at hy
    rcases hy with ⟨xs, yv⟩
    rcases xs with ⟨ x, xsx, rfl⟩
    simp
    use x
  exact subset_antisymm h6 h4

  /- another shorter way of proving it:

  example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  simp only [mem_inter_iff, mem_image, mem_preimage]
  constructor
  · rintro ⟨⟨x, xs, rfl⟩, yv⟩
    exact ⟨x, ⟨xs, yv⟩, rfl⟩
  · rintro ⟨x, ⟨xs, fxv⟩, rfl⟩
    exact ⟨⟨x, xs, rfl⟩, fxv⟩

  -/

 #check image_inter_subset
 #check image_preimage_subset
 #check image_inter_subset
 #check subset_trans
 #check inter_subset_left
 #check monotone_image
 #check subset_antisymm
 #check preimage_inter
 #check subset_preimage_image
 #check preimage_union
 #check union_subset_union_left
 #check inter_subset_inter_left
 #check image_iInter_subset


example {r: Set α} (h : s ⊆ t) : s ∩ r ⊆ t ∩ r :=
  fun _x ⟨xs, xr⟩ ↦ ⟨h xs, xr⟩


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u :=
  fun _y⟨x,  ⟨xs, xfu⟩, fxy⟩ ↦ ⟨ ⟨x, xs, fxy⟩ , by simpa  [← fxy, xfu]⟩
 -- fun _y ⟨x, ⟨xs, xfu⟩, fxy⟩ ↦ ⟨⟨x, xs, fxy⟩, fxy ▸ xfu⟩
  --fun _y ⟨x, ⟨xs, xfu⟩, fxy⟩ ↦ ⟨⟨x, xs, fxy⟩, by rw [← fxy]; exact xfu⟩


example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
   rw[preimage_inter]
   intro x ⟨xs, xfu⟩
   constructor
   · apply subset_preimage_image
     exact xs
   · exact xfu

/- shorter proof:
example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rw [preimage_inter]
  exact inter_subset_inter_left _ (subset_preimage_image f s)
-/



example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rw[preimage_union]
  exact union_subset_union_left _ (subset_preimage_image f s)

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · intro hy
    simp at hy
    simp
    rcases hy with ⟨x, ⟨ xAi, fxy⟩ ⟩
    rcases xAi with ⟨i, hyxi⟩
    use i,x
  · intro h
    simp at h
    simp
    rcases h with ⟨ i, x, ⟨ xAi, fxy⟩ ⟩
    use x
    constructor
    · use i
    · exact fxy

 /- ANother, shorter proof using rintro:

 example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, rfl⟩
    exact ⟨i, x, xAi, rfl⟩
  · rintro ⟨i, x, xAi, rfl⟩
    exact ⟨x, ⟨i, xAi⟩, rfl⟩
 -/


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  exact image_iInter_subset (fun i ↦ A i) f

/- can write the line
apply image_iInter_subset (fun i ↦ A i) f
as
apply image_iInter_subset
or
apply image_iInter_subset _ f

Following is the proof of this exact ready-made theorem
-/
example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y hy
  simp at hy
  simp
  rcases hy with ⟨x, xAi, hyx, rfl⟩
  intro i
  specialize  xAi i
  use x

/- No need of hyx, can replace rcases line with:
 rcases hy with ⟨x, xAi, hyx, rfl⟩
-/

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y hy
  simp at hy
  simp
  have hyi:∃ x ∈ A i, f x = y:= by
    exact hy i
  rcases hyi with ⟨x, hyx, rfl⟩
  use x
  constructor
  · intro j
    specialize hy j
    rcases hy with ⟨ z, hyjz,fzx⟩
    have h: x = z := by
      apply injf at fzx
      exact fzx.symm
    rw[← h] at hyjz
    exact hyjz
  · rfl




example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  · intro h
    simp
    simp at h
    rcases h with ⟨i, hi⟩
    use i
  · intro h
    simp at h
    simp
    exact h

/- shorter proof:
example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp
-/
example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  · intro h
    have h1: f x ∈ ⋂ i, B i := h
    have h2: ∀ i, f x ∈  B i := by
      /- These two lines can be  replaced by the rwa line below
        rw[mem_iInter] at h1
        exact h1
        -/
      rwa [mem_iInter] at h1
    have h3: ∀ i, x∈ f⁻¹' B i:= h2
    rw[mem_iInter]
    exact h3
  · intro h
    rw[mem_iInter] at h
    have h1: ∀ (i: I), f x∈ B i:=h
    rw[← mem_iInter] at h1
    exact h1

/- example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp
  -/

#check mem_iInter
#check  InjOn
#check sq_sqrt
example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg h
  calc
    x = (sqrt x) ^ 2 := by
     rw[sq_sqrt xnonneg]
    _ = (sqrt y) ^ 2 := by rw[h]
    _ = y            := sq_sqrt ynonneg

#check sq_sqrt
#check sqrt_sq
#check sqrt_nonneg

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg h
  simp at h
  calc
    x = sqrt (x ^ 2)  := by
      rw[sqrt_sq xnonneg]
    _ =  sqrt (y ^ 2) := by rw[h]
    _ = y             :=  sqrt_sq ynonneg

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext z
  constructor
  · intro h
    simp at h
    rcases h with ⟨x, hx⟩
    simp
    have h1: √x ≥ 0 := sqrt_nonneg x
    rw[hx.right] at h1
    exact h1
  · intro h
    --simp at h
    --simp
    use (z ^ 2)
    exact ⟨sq_nonneg z, sqrt_sq h⟩




example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext  z
  constructor
  · intro h
    --simp at h
    --simp
    rcases h with ⟨x, hx⟩
    rw[← hx]
    exact sq_nonneg x
  · intro h
    --simp at h
    --simp
    use (sqrt z)
    exact sq_sqrt h

 /-  another shorter proof using rintro in place of intro+rcases:
 example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact sq_nonneg x
  · intro h
    exact ⟨sqrt z, sq_sqrt h⟩

 -/

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dite_eq_left h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h₁ x
    have h₂: f (inverse f (f x))=f x:= by
      apply inverse_spec (f x) ⟨x,rfl⟩
    exact h₁  h₂
  · intro h₁ x y h₂
    have h₃: (inverse f) (f x) = (inverse f) (f y):= by rw[h₂ ]
    --rw[h₁] at h₃
    --rw[h₁] at h₃
    --exact h₃
    rw [h₁, h₁] at h₃
    exact h₃

/-the last 3 lines of code can be replace by:
rw [h₁, h₁] at h₃
-/


example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h₁ y
    apply inverse_spec y (h₁ y)
  · intro h₁ y
    use (inverse f) y
    exact h₁ y




end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S:= by
    exact h₁
  have h₃ : j ∉ S:= by
    rw[h] at h₁
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
