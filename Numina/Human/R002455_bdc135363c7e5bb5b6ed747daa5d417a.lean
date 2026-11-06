import Mathlib

/- Given a real number x, let ⌊x⌋ denote the greatest integer less than or equal to x. For a certain integer k, there are exactly 70 positive integers n_1, n_2, ..., n_70 such that k = ⌊\sqrt[3]{n_1}⌋ = ⌊\sqrt[3]{n_2}⌋ = ... = ⌊\sqrt[3]{n_70}⌋ and k divides n_i for all i such that 1 ≤ i ≤ 70. Find the maximum value of n_i / k for 1 ≤ i ≤ 70 -/
theorem number_theory_93654 (k : ℕ) (h₀ : k > 0) (h₁ : {n : ℕ | n > 0 ∧ k = ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋ ∧ k ∣ n}.ncard = 70) :
IsGreatest {x | ∃ n : ℕ, n > 0 ∧ k = ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋ ∧ k ∣ n ∧ x = n / k} 553 := by
  -- we'll prove injection from [k^2, k^2+3k+3] and the provided set, f(x) = kx will be used as injection
  let f (x: ℕ) := x * k
  -- prove injective property
  have hfinj: Function.Injective f := by
    rintro x y hfx_eq_fy
    simp [f] at hfx_eq_fy
    apply Or.resolve_right hfx_eq_fy
    linarith
  -- prove that k = ⌊n^(1/3⌋ ↔ k^3 ≤ n ≤ (k+1)^3-1
  have hn_bounds (n: ℕ) : k = ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋ ↔ k^3 ≤ n ∧ n ≤ (k+1)^3-1 := by
    rw [eq_comm]
    rw [Int.floor_eq_iff]
    norm_cast
    have : ((n:ℝ)^((1:ℝ)/3))^3 = n := by calc
      ((n:ℝ)^((1:ℝ)/3))^3 = ((n:ℝ)^((1:ℝ)/3))^(3:ℝ) := by norm_cast
      _ = n := by simp
    have aux1 : k ≤ (n:ℝ)^((1:ℝ)/3) ↔ k^3 ≤ n := by
      nth_rw 1 [← pow_le_pow_iff_left₀ _ _ (by norm_num: 3 ≠ 0)]
      . rw [this]
        norm_cast
      . positivity
      . positivity
    have aux2 : (n:ℝ)^((1:ℝ)/3) < ↑(k+1) ↔ n < (k+1)^3 := by
      nth_rw 1 [← pow_lt_pow_iff_left₀ _ _ (by norm_num: 3 ≠ 0)]
      . rw [this]
        norm_cast
      . positivity
      . positivity
    have aux3 : n < (k+1)^3 ↔ n ≤ (k+1)^3 - 1 := by
      have : 1^3 < (k+1)^3 := by refine Nat.pow_lt_pow_left ?_ ?_ <;> omega
      constructor <;> (intro; omega)
    rw [aux3] at aux2
    rw [aux1, aux2]
  simp_rw [hn_bounds]
  simp_rw [hn_bounds] at h₁
  -- next prove that target set is image of f over [k^2, k^2+3k+3]
  have hf_img : {n | n > 0 ∧ (k ^ 3 ≤ n ∧ n ≤ (k + 1) ^ 3 - 1) ∧ k ∣ n} = f '' (Set.Icc (k^2) (k^2 +3*k+3)) := by
    ext x
    constructor
    . rintro ⟨hn, ⟨hk_lb, hk_ub⟩, hk_dv⟩
      obtain ⟨c, hc⟩ := hk_dv
      use c
      constructor
      any_goals constructor
      . calc
          k^2 = k^2 * k / k := by field_simp
          _ = k^3 / k := by ring_nf
          _ ≤ x / k := by gcongr
          _ = c := by rw [hc]; field_simp
      . calc
          c = x / k := by rw [hc]; field_simp
          _ ≤ ((k + 1) ^ 3 - 1) / k := by gcongr
          _ = (k * 3 + k ^ 2 * 3 + k ^ 3 + 1 - 1) / k := by ring_nf
          _ = (k * 3  + k ^ 2 * 3 + k ^ 3) / k := by congr
          _ = k * (k^2 + 3*k + 3) / k := by ring_nf
          _ = k^2 + 3*k + 3 := by field_simp
      . rw [hc]; dsimp [f]; ring
    . rintro ⟨c, ⟨⟨hc_lb, hc_ub⟩, hc_f⟩⟩
      have : 0 < c := by calc
          0 < k^2 := by exact Nat.pos_pow_of_pos 2 h₀
          _ ≤ c := by exact hc_lb
      dsimp [f] at hc_f
      constructor
      any_goals constructor
      . rw [← hc_f]
        positivity
      . constructor
        . calc
          k^3 = k^2 * k := by ring
          _ ≤ c * k := by gcongr
          _ ≤ x := by rw [hc_f]
        . calc
          x = c * k := by rw [hc_f]
          _ ≤ (k ^ 2 + 3 * k + 3) * k := by gcongr
          _ = k^3 + 3 * k^2 + 3 * k := by ring
          _ = k^3 + 3 * k^2 + 3 * k + 1 - 1 := by rfl
          _ = (k + 1) ^ 3 - 1 := by ring_nf
      . rw [← hc_f]
        exact Nat.dvd_mul_left k c
  -- previous fact means 70 = #([k^2, k^2+3k+3]) = 3k + 4, so k = 22
  have : 70 = 3 * k + 4 := by
    calc
      70 = {n | n > 0 ∧ (k ^ 3 ≤ n ∧ n ≤ (k + 1) ^ 3 - 1) ∧ k ∣ n}.ncard := by rw [h₁]
      _ = (f '' (Set.Icc (k^2) (k^2 +3*k+3))).ncard := by rw [hf_img]
      _ = (Set.Icc (k ^ 2) (k ^ 2 + 3 * k + 3)).ncard := by exact Set.ncard_image_of_injective _ hfinj
      _ = Nat.card (Set.Icc (k ^ 2) (k ^ 2 + 3 * k + 3)) := by rw[Set.Nat.card_coe_set_eq]
      _ = (k^2 + 3*k + 3) + 1 - (k^2) := by simp
      _ = 3 * k + 4 := by omega
  have : k = 22 := by omega
  -- now just prove that 553 is greatest by showng that it is inside the target set and divisible by 22
  -- and that any element is less than it (as 12166 = 553 * (3*22^2+3*22+1))
  subst k
  norm_num
  constructor
  . use 12166
    norm_num
  . rintro x ⟨n, hn_pos, ⟨hn_lb, hn_ub⟩, hn_dv, hxn⟩
    omega