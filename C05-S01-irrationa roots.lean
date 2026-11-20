import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two
#check Nat.prime_two.dvd_mul
#check Nat.Prime.dvd_mul
#check Nat.prime_zero_false
theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    have h: 2 ∣ m ^ 2 := by
     norm_num[sqr_eq]
    exact even_of_even_sqr h    
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := 
     (mul_right_inj' two_ne_zero).mp this
  have : 2 ∣ n := by
    have h1: 2 ∣ n ^ 2 := by
      norm_num[this.symm]
    exact even_of_even_sqr h1  
  have : 2 ∣ (m.gcd n) := by
    apply dvd_gcd ‹ 2 ∣ m ›  this
  have : 2 ∣ 1 := by
    rwa[coprime_mn] at this 
  norm_num at this

#check dvd_gcd

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have : p ∣ m := by
    have h: p ∣ m ^ 2 := by
     norm_num[sqr_eq]
    rw[pow_two, Nat.Prime.dvd_mul prime_p] at h
    cases h <;> assumption   
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    have k: p≠ 0:= by 
      intro l
      apply Nat.prime_zero_false
      rw[l] at prime_p
      exact prime_p
      --apply prime_p at l
    exact (mul_right_inj' k).mp this
  have : p ∣ n := by
    have h1: p ∣ n ^ 2 := by
      norm_num[this.symm]
    rw[pow_two, Nat.Prime.dvd_mul prime_p] at h1
    cases h1 <;> assumption   
  have : p ∣ (m.gcd n) := by
    apply dvd_gcd ‹ p ∣ m ›  this
  have : p ∣ 1 := by
    rwa[coprime_mn] at this
  have h2: p = 1 :=  by
    simp at this
    exact this
  rw[h2] at prime_p
  apply Nat.prime_one_false at prime_p
  exact prime_p
  
/-
proving p≠ 0 in one term:
have : p * k ^ 2 = n ^ 2 :=
  (mul_right_inj' prime_p.ne_zero).mp this
can use this line for closing p|:
exact prime_p.not_dvd_one this
Reusing the p ∣ x ^ 2 → p ∣ x logic: 
•  Notice you proved p ∣ m ^ 2 → p ∣ m and p ∣ n ^ 2 → p ∣ n using the exact same three lines. You can bind that mini-lemma once with have dvd_of_dvd_sqr : ∀ x, p ∣ x ^ 2 → p ∣ x (or use Mathlib's prime_p.dvd_of_dvd_pow) to avoid repeating the rw and cases block.

-/
    

#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique
#check Nat.divisors_one
#check Nat.prime_one_false
#check Nat.prime_zero_false


theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw[Nat.factorization_pow]
    rfl
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw[factorization_mul' prime_p.ne_zero nsqr_nez, Nat.Prime.factorization' prime_p, Nat.factorization_pow]
    rw[add_comm]
    rfl
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (eq_zero_of_pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw[factorization_pow' m k p]
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    rw[factorization_mul' (Nat.succ_ne_zero r) npow_nz p,factorization_pow' n k p, add_comm ]
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  use m.factorization p - n.factorization p
  rw[← Nat.mul_sub_left_distrib  k (m.factorization p)  (n.factorization p)]
  

#check multiplicity

