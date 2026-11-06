import Mathlib

open Real

/-Find the number of integers $n$ such that

$$
1+\left\lfloor\frac{100 n}{101}\right\rfloor=\left\lceil\frac{99 n}{100}\right\rceil
$$-/
theorem number_theory_609075 : {n : ℤ | 1 + ⌊(100 * n / 101 : ℝ)⌋ = ⌈(99 * n / 100 : ℝ)⌉}.ncard = 10100 := by
  obtain ⟨f, hf₁⟩ := show ∃f : ℤ → ℤ, ∀ n, f n = ⌈(99 * n / 100 : ℝ)⌉ - ⌊(100 * n / 101 : ℝ)⌋ by
    use fun n => ⌈(99 * n / 100 : ℝ)⌉ - ⌊(100 * n / 101 : ℝ)⌋
    simp
  have hf₂ : ∀ n, f (n + 10100) = f n - 1 := by
    intro n
    rw [hf₁]
    have h₁ : ⌈(99 * (n + 10100 : ℤ) / 100 : ℝ)⌉ = ⌈(99 * n / 100 : ℝ)⌉ + 99 * 101 := by
      have : (99 * (n + 10100 : ℤ) / 100 : ℝ) = (99 * n / 100 : ℝ) + (99 * 101 : ℤ) := by
        norm_num
        linarith
      rw [this, Int.ceil_add_int]
    rw [h₁]
    have h₂ : ⌊(100 * (n + 10100 : ℤ) / 101 : ℝ)⌋ = ⌊(100 * n / 101 : ℝ)⌋ + 100^2 := by
      have : (100 * (n + 10100 : ℤ) / 101 : ℝ) = (100 * n / 101 : ℝ) + (100^2 : ℤ) := by
        norm_num
        linarith
      rw [this, Int.floor_add_int]
    rw [h₂, hf₁]
    linarith
  have h₁ : {n : ℤ | 1 + ⌊(100 * n / 101 : ℝ)⌋ = ⌈(99 * n / 100 : ℝ)⌉} = {n : ℤ | f n = 1} := by
    ext n; simp
    rw [hf₁]
    omega
  have hf₃ : ∀ n ≥ 0, n < 10100 → ∃! k, f (k * 10100 + n) = 1 := by
    intro n hn₁ hn₂
    obtain ⟨g, hg₁⟩ := show ∃g : ℤ → ℤ, g = fun k => f (k * 10100 + n) by simp
    apply Function.Bijective.existsUnique ?_ 1
    rw [←hg₁]
    have hg₂ : ∀ m, g (m + 1) = g m - 1 := by
      intro m
      rw [hg₁]
      ring_nf
      rw [show 10100 + m * 10100 + n = (m * 10100 + n) + 10100 by ring_nf, hf₂]
      ring_nf
    obtain ⟨q, hq⟩ := show ∃q : ℤ, q = g 0 by simp
    have hg₃ : g = λm ↦ q - m := by
      have : ∀ (n : ℤ) (m : ℕ), g (n + m) = g n - m := by
        intro n m
        induction' m using Nat.strongRec with m hm
        by_cases hm₁ : m = 0
        · rw [hm₁]
          norm_num
        specialize hm (m - 1) (by omega)
        rw [show n + (m - 1 : ℕ) = (n + m) - 1 by omega] at hm
        rw [show n + m = (n + m - 1) + 1 by omega, hg₂]
        omega
      ext x
      rw [hq]
      by_cases hx: 0 ≤ x
      · specialize this 0 x.natAbs
        norm_num at this
        rw [abs_of_nonneg hx] at this
        exact this
      push_neg at hx
      specialize this x x.natAbs
      simp at this
      rw [abs_of_neg hx] at this
      norm_num at this
      linarith
    rw [hg₃]
    constructor
    · -- Function.Injective
      intro x y
      simp
    · -- Function.Surjective
      intro x
      simp
      use q - x
      linarith
  rw [h₁]

  suffices (Finset.Ico (0 : ℤ) 10100 : Set ℤ).ncard = {n : ℤ | f n = 1}.ncard by
    rw [←this, Set.ncard_coe_Finset]
    native_decide
  have hf₄ : ∀n ≥ 0, n < 10100 → ∃ k, f (k * 10100 + n) = 1 := by
    intro n hn₁ hn₂
    obtain ⟨k, hk₁, hk₂⟩ := hf₃ n hn₁ hn₂
    use k
  have h₂ : ∀ n ∈ ↑(Finset.Ico (0 : ℤ) 10100), 0 ≤ n ∧ n < 10100 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact hn

  apply Set.ncard_congr
  case f => exact (λn hn ↦ Classical.choose (hf₄ n (h₂ n hn).left (h₂ n hn).right) * 10100 + n)
  simp
  rintro n ⟨hn₁, hn₂⟩
  apply Classical.choose_spec (hf₄ n hn₁ hn₂)
  simp
  rintro a b ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩ heq₁
  omega
  simp
  intro n hn₁
  obtain ⟨k, r, hk, hr₁, hr₂⟩ := show ∃k r : ℤ, n = k * 10100 + r ∧ 0 ≤ r ∧ r < 10100 by
    use n / 10100, n % 10100
    omega
  use r, (by omega)
  have ⟨p, hp₁, hp₂⟩ := hf₃ r hr₁ hr₂
  rw [hk] at hn₁ ⊢
  linarith [hp₂ k hn₁, hp₂ _ (Classical.choose_spec (hf₄ r hr₁ hr₂))]
