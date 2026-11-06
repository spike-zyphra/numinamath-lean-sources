import Mathlib

open ArithmeticFunction

theorem number_theory_114470 (a b c d : ℕ) (ha : a < b) (hb : b < c) (hc : c < d)
    (h : a * b * c * d = 2014) :
    (a ^ 2014 + b ^ 2014 + c ^ 2014 + d ^ 2014) % 10 = 5 := by
  suffices H : a = 1 ∧ b = 2 ∧ c = 19 ∧ d = 53 by
    rcases H with ⟨rfl, rfl, rfl, rfl⟩
    native_decide
  have h₀ : 2014 = 2 * 19 * 53 := by simp
  have h₁ : a ≠ 0 := by rintro rfl; simp at h
  have h₂ : b ≠ 0 := by rintro rfl; simp at h
  have h₂' : 1 < b := by omega
  have h₃ : c ≠ 0 := by rintro rfl; simp at h
  have h₃' : 1 < c := by omega
  have h₄ : d ≠ 0 := by rintro rfl; simp at h
  have h₄' : 1 < d := by omega
  have H := congrArg Ω h
  rw [h₀] at H
  repeat rw [cardFactors_mul (by positivity) (by positivity)] at H
  norm_num at H
  have k₁ {x} (hx : 1 < x) : 0 < Ω x := by
    by_contra! K
    simp [cardFactors] at K
    omega
  have h₂'' : 0 < Ω b := k₁ h₂'
  have h₃'' : 0 < Ω c := k₁ h₃'
  have h₄'' : 0 < Ω d := k₁ h₄'
  have h₁'' : Ω a = 0 := by omega
  replace h₂'' : Ω b = 1 := by omega
  replace h₃'' : Ω c = 1 := by omega
  replace h₄'' : Ω d = 1 := by omega
  simp [cardFactors, h₁] at h₁''
  rcases h₁'' with rfl
  simp at h₂'' h₃'' h₄'' h ⊢
  have k₂ {x} (hx : x ∣ 2014) (hx' : x.Prime) : x ∈ ({2, 19, 53} : Finset ℕ) := by
    convert Nat.mem_primeFactors.mpr ⟨hx', hx, by simp⟩
    native_decide
  have hb' : b ∈ ({2, 19, 53} : Finset ℕ) := k₂ ⟨c * d, by linear_combination -h⟩ h₂''
  have hc' : c ∈ ({2, 19, 53} : Finset ℕ) := k₂ ⟨b * d, by linear_combination -h⟩ h₃''
  have hd' : d ∈ ({2, 19, 53} : Finset ℕ) := k₂ ⟨b * c, by linear_combination -h⟩ h₄''
  clear * - hb hc hb' hc' hd' h
  suffices H : ∀ b ∈ ({2, 19, 53} : Finset ℕ), ∀ c ∈ ({2, 19, 53} : Finset ℕ), ∀ d ∈ ({2, 19, 53} : Finset ℕ), b * c * d = 2014 → b < c → c < d → b = 2 ∧ c = 19 ∧ d = 53 from H b hb' c hc' d hd' h hb hc
  native_decide
