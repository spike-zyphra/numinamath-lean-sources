import Mathlib

/- Let $a_1,a_2,\ldots$ be a sequence determined by the rule $a_n=a_{n-1}/2$ if $a_{n-1}$ is even and $a_n=3a_{n-1}+1$ if $a_{n-1}$ is odd. For how many positive integers $a_1 \le 2008$ is it true that $a_1$ is less than each of $a_2$, $a_3$, and $a_4$?
$\mathrm{(A)}\ 250\qquad\mathrm{(B)}\ 251\qquad\mathrm{(C)}\ 501\qquad\mathrm{(D)}\ 502\qquad\mathrm{(E)} 1004$ -/
theorem number_theory_98536 :
  Set.ncard {x | (0 < x ∧ x ≤ 2008) ∧ ∃ a : ℕ → ℕ, a 1 = x ∧ (∀ n ≥ 1, a (n + 1) = if Even (a n) then a n / 2 else 3 * a n + 1) ∧ (a 1 < a 2 ∧ a 1 < a 3 ∧ a 1 < a 4)
  } = 502 := by
  -- define a smaller name for ease of proof
  set validRecursion := fun (a: ℕ → ℕ) ↦  ∀ n ≥ 1, a (n + 1) = if Even (a n) then a n / 2 else 3 * a n + 1
  -- auxilary fact that a(n) even means a(n+1) = a(n)/2 for n ≥ 1
  have h_even {a: ℕ → ℕ} {n: ℕ} (hv: validRecursion a) (h': Even (a n)) (h'': n ≥ 1) : a (n+1) = a n / 2 := by
    have := hv n
    simp [h'] at this
    exact this h''
  -- auxilary fact that a(n) odd means a(n+1) = 3a(n)+1 for n ≥ 1
  have h_odd {a: ℕ → ℕ} {n: ℕ} (hv: validRecursion a) (h': Odd (a n)) (h'': n ≥ 1) : a (n+1) = 3 * a n + 1  := by
    have := hv n
    simp [Nat.not_even_iff_odd.mpr h'] at this
    exact this h''
  -- prove that for valid recursions, a(1) is less then a(2), a(3), a(4) iff a(1) % 4 = 3
  have h_f_eqv {a : ℕ → ℕ} (hv : validRecursion a) : (a 1 < a 2 ∧ a 1 < a 3 ∧ a 1 < a 4) ↔ (a 1) % 4 = 3 := by
    -- prove it by case work on a(1) % 4 as a(1) = 4k + (a(1) % 4)
    have h4n : a 1 = 4 * (a 1 / 4) + (a 1 % 4) := by  exact Eq.symm (Nat.div_add_mod (a 1) 4)
    set k := a 1 / 4
    have : a 1 % 4 < 4 := by simp [Nat.mod_lt]
    interval_cases (a 1 % 4)
      -- for a(1) = 4k, a(2) = 2k ≤ a(1)
    . have : a 1 = 2 * (2 * k) := by rw [h4n]; ring
      have : Even (a 1) := by rw [this]; exact even_two_mul _
      have h₂ : a (1 + 1) = 2 * k := by rw [h_even hv this, h4n] <;> omega
      simp at h₂
      have : a 2 ≤ a 1 := by rw [h4n, h₂]; omega
      simp; intro; omega
      -- for a(1) = 4k+1, a(2) = 12k + 4, a(3) = 6k + 2, a(4) = 3k+1 ≥ a(1)
    . have : a 1 = 2 * (2 * k) + 1 := by rw [h4n]; ring
      have : Odd (a 1) := by rw [this]; exact odd_two_mul_add_one _
      have h₂ : a (1 + 1) = 2 * (6 * k + 2) := by rw [h_odd hv this, h4n] <;> omega
      have : Even (a (1 + 1)) := by rw [h₂]; exact even_two_mul _
      simp at this
      have h₃ : a (2 + 1) = 2 * (3 * k + 1) := by rw [h_even hv this, h₂] <;> omega
      have : Even (a (2 + 1)) := by rw [h₃]; exact even_two_mul _
      simp at this
      have h₄ : a (3 + 1) = 3 * k + 1 := by rw [h_even hv this, h₃] <;> omega
      simp at h₄
      have : a 4 ≤ a 1 := by rw [h4n, h₄]; omega
      simp; rintro _ _; omega
      -- for a(1) = 4k+2, a(2) = 2k+1 ≤ a(1)
    . have : a 1 = 2 * (2 * k + 1) := by rw [h4n]; ring
      have : Even (a 1) := by rw [this]; exact even_two_mul _
      have h₂ : a (1 + 1) = 2 * k + 1 := by rw [h_even hv this, h4n] <;> omega
      simp at h₂
      have : a 2 ≤ a 1 := by rw [h4n, h₂]; omega
      simp; intro; omega
      -- for a(1) = 4k+3, we have a(2), a(3), a(4) all larger than a(1)
    . have : a 1 = 2 * (2 * k + 1) + 1 := by rw [h4n]; ring
      have : Odd (a 1) := by rw [this]; exact odd_two_mul_add_one _
      have h₂ : a (1 + 1) = 2 * (6 * k + 5) := by rw [h_odd hv this, h4n] <;> omega
      have : Even (a (1 + 1)) := by rw [h₂]; exact even_two_mul _
      simp at this
      have h₃ : a (2 + 1) = 2 * (3 * k + 2) + 1 := by rw [h_even hv this, h₂] <;> omega
      have : Odd (a (2 + 1)) := by rw [h₃]; exact odd_two_mul_add_one _
      simp at this
      have h₄ : a (3 + 1) = 18 * k + 16 := by rw [h_odd hv this, h₃] <;> omega
      have h₂ : a 1 < a 2 := by rw [h4n, h₂]; omega
      have h₃ : a 1 < a 3 := by rw [h4n, h₃]; omega
      have h₄ : a 1 < a 4 := by rw [h4n, h₄]; omega
      simp [h₂, h₃, h₄]
  -- next prove that there is validRecursion a with a(1) = x  and a(1) < a(2), a(3), a(4) iff x ≡ 3 [MOD 4]
  have h_x_eqv (x : ℕ) : (∃ a : ℕ → ℕ, a 1 = x ∧ validRecursion a ∧ (a 1 < a 2 ∧ a 1 < a 3 ∧ a 1 < a 4)) ↔ (x ≡ 3 [MOD 4]) := by
    constructor
      -- → side is easy from previous proved equivalence
    . rintro ⟨a, h₁, h₂, h₃⟩
      have := (h_f_eqv h₂).mp h₃
      rw [h₁] at this
      exact this
      -- ← side, we present the sequence a with a(0) = 2x and a(n+1) = if Even a_n then a_n / 2 else 3 * a_n + 1
    . rintro hx
      set a : ℕ → ℕ := fun n => Nat.recOn n (2 * x) (fun n a_n => if Even a_n then a_n / 2 else 3 * a_n + 1) with ha
      use a
      have hx' : a 1 = x := by simp [a]
      constructor
      . exact hx'
      . have hv: validRecursion a := by
          rintro n _
          nth_rw 1 [ha]
        have := (h_f_eqv hv).mpr
        nth_rw 1 [hx'] at this
        exact ⟨hv, this hx⟩
  -- form previous facts we prove that the set is basically {x ∈ (0 2008] | x ≡ 3 [MOD 4]}
  have : {x | (0 < x ∧ x ≤ 2008) ∧ ∃ a, a 1 = x ∧ validRecursion a ∧ a 1 < a 2 ∧ a 1 < a 3 ∧ a 1 < a 4} = {x ∈ Set.Ioc 0 2008 | x ≡ 3 [MOD 4]} := by
    ext x
    simp
    rintro _ _
    exact h_x_eqv x
  -- now we use cadinality formula to find that cardinality is (⌊(2008 - 3) / 4⌋ - ⌊(0 - 3) / 4⌋) = 502
  rw [this]
  calc
    {x | x ∈ Set.Ioc 0 2008 ∧ x ≡ 3 [MOD 4]}.ncard = Nat.card {x | x ∈ Set.Ioc 0 2008 ∧ x ≡ 3 [MOD 4]} := by rw[Set.Nat.card_coe_set_eq]
    _ = (Finset.filter (fun x => x ≡ 3 [MOD 4]) (Set.Ioc 0 2008).toFinset).card  := by
      rw [Nat.card_eq_fintype_card]
      rw [Fintype.card_ofFinset]
    _ = (Finset.filter (fun x => x ≡ 3 [MOD 4]) (Finset.Ioc 0 2008)).card  := by
      simp
    _ = 502 := by
      have : 4 > 0 := by omega
      zify
      rw [Nat.Ioc_filter_modEq_card 0 2008 this 3]
      norm_num