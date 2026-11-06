import Mathlib

set_option push_neg.use_distrib true

lemma powerset_singleton {n : ℕ}
  : ({n} : Finset ℕ).powerset = {∅, {n}}
  := by rfl

lemma singleton_insert_eq_union {n : ℕ} (s : Finset (Finset ℕ))
  : insert ({n} : Finset ℕ) s = ({{n}} : Finset (Finset ℕ)) ∪ s
  := by rfl

lemma powerset_cases {n₁ n₂ n₃ : ℕ}
  : ({n₁, n₂, n₃} : Finset ℕ).powerset =
  {{}, {n₁}, {n₂}, {n₃}, {n₁, n₂}, {n₂, n₃}, {n₁, n₃}, {n₁, n₂, n₃}} := by
  simp_all [
    Finset.powerset_insert, Finset.insert_comm,
    powerset_singleton, <- singleton_insert_eq_union
  ]
  congr!

lemma sqrt_linear_independence {A B : ℚ} (pos_a : 0 < A) (pos_b : 0 < B)
  (hA : Irrational (Real.sqrt A)) (hB : Irrational (Real.sqrt B))
  (hAB : Irrational (Real.sqrt (A * B))) {u v r : ℚ} :
  u * Real.sqrt A + v * Real.sqrt B = r →
  u = 0 := by
  intro h
  have rational_sum : ¬Irrational (↑u * √↑A + ↑v * √↑B) := by
    contrapose! h
    rw [irrational_iff_ne_rational] at h
    specialize h r.num r.den
    convert h
    norm_cast
    simp

  have h_sq1 : (u * Real.sqrt A + v * Real.sqrt B)^2 = r^2 := by rw [h]
  simp [add_sq] at h_sq1
  have h_AB_part : 2 * u * v * Real.sqrt (A * B)
      = r^2 - u^2 * A - v^2 * B := by
    ring_nf at h_sq1
    rw [Real.sqrt_mul (by positivity)]
    rw [<- h_sq1]
    ring_nf
    simp [mul_comm, mul_assoc]
    conv_lhs => rw [<- add_zero (2 * (↑u * (↑v * (√↑A * √↑B))))]
    congr
    conv_lhs => rw [<- add_zero (2 * (↑u * (↑v * (√↑A * √↑B))))]
    congr
    all_goals
      rw [Real.sq_sqrt (by positivity), mul_comm]
      simp
  have : ¬Irrational (↑(2:ℚ) * ↑u * ↑v * √(↑A * ↑B)) := by
    rw_mod_cast [h_AB_part]
    intro irr
    simp only [Rat.not_irrational] at irr

  rw_mod_cast [irrational_rat_mul_iff] at this
  push_neg at this
  simp only [hAB] at this
  simp at this
  cases this
  · assumption
  · simp_all
    have : u = 0 ∨ Irrational (u * √↑A) := by
      simp [hA, irrational_rat_mul_iff]
      exact eq_or_ne u 0
    rcases this with (_ | irr_mul)
    · assumption
    · rw [h] at irr_mul
      simp only [Rat.not_irrational] at irr_mul

theorem number_theory_641689 {n₁ n₂ n₃ : ℕ} (pos_n₁ : 0 < n₁)
  (pos_n₂ : 0 < n₂) (pos_n₃ : 0 < n₃)
  (card_3 : ({n₁, n₂, n₃} : Finset ℕ).card = 3)
  : (∀ s : Finset ℕ, s ⊆ {n₁, n₂, n₃} → s.Nonempty →
    ¬ IsSquare (s.prod id)) →
    Irrational (Real.sqrt n₁ + Real.sqrt n₂ + Real.sqrt n₃)
    := by
  intro h
  obtain ⟨ ne₁_₂, ne₂_₃, ne₁_₃ ⟩ : n₁ ≠ n₂ ∧ n₂ ≠ n₃ ∧ n₁ ≠ n₃ := by
    split_ands
    all_goals
      intro eq
      subst eq
      simp [Finset.card_insert_eq_ite] at card_3
      split_ifs at card_3 <;> contradiction

  by_contra hr
  rw [irrational_iff_ne_rational] at hr
  simp [<- Finset.mem_powerset] at h
  rw [powerset_cases] at h
  simp at h
  obtain ⟨ h₁, h₂, h₃, h₄, h₅, h₆, h₇ ⟩ := h
  push_neg at hr
  simp_all
  obtain ⟨a, b, sum_eq_rat⟩ := hr
  generalize hr : (a : ℚ) / b = q
  rw_mod_cast [hr] at sum_eq_rat

  have : √↑n₁ + √↑n₂ = q - √↑n₃ := by linarith
  replace : (√↑n₁ + √↑n₂)^2 = (q - √↑n₃)^2 := by
    exact congrArg (· ^ 2) this
  replace : (√↑n₁)^2 + (√↑n₂)^2 + (2 * (√↑n₁) * (√↑n₂)) = (q - √↑n₃)^2 := by
    linarith
  replace : n₁ + n₂ + (2 * (√↑n₁) * (√↑n₂)) = (q - √↑n₃)^2 := by
    simpa [Real.sqrt_sq] using this
  replace : n₁ + n₂ + (2 * (√↑n₁) * (√↑n₂)) = q^2 - 2 * q * √↑n₃ + n₃ := by
    simpa [sub_sq] using this
  replace : (2 * (√↑n₁) * (√↑n₂)) + 2 * q * √↑n₃ = q^2 + n₃ - n₁ - n₂ := by
    linarith

  rw [<- irrational_sqrt_natCast_iff] at *

  simpa using sqrt_linear_independence
    (by positivity) (mod_cast pos_n₃) h₄ h₃
    (u := 2) (v := 2*q) (r := q^2 + n₃ - n₁ - n₂)
    (by simpa [mul_assoc] using h₇)
    (by simpa [mul_assoc] using this)
