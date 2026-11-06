import Mathlib

open Set

/- 1. $[x]$ represents the greatest integer not greater than $x$. In the set $\left\{\left[\frac{1^{2}}{2005}\right],\left[\frac{2^{2}}{2005}\right], \cdots,\left[\frac{2005^{2}}{2005}\right]\right\}$, the number of distinct elements is
A. 1503
B. 1504
C. 1505
D. 2005 -/

-- the function that is applied on each value of 1 to 2005
noncomputable
def f (x : ℕ) := ⌊(x^2 : ℝ) / 2005⌋

-- f is monotonic, as square by 2005 is strict monotonic and flooring is monotoinc
lemma l_f_mono : Monotone f := by
  rintro x y hxy
  replace hxy : (x : ℝ)^2 ≤ y^2 := by
    rw [sq_le_sq₀ (by positivity) (by positivity)]
    norm_cast
  have : (x^2 : ℝ) / 2005 ≤ (y^2 : ℝ) / 2005 := by linarith
  simp [f]
  apply Int.floor_mono
  assumption

-- we can write the set as disjoin union of f''[1, 1001] and f''[1002, 2005]
lemma l_union : (f '' (Icc 1 2005)).ncard = (f '' (Icc 1 1001)).ncard + (f '' (Icc 1002 2005)).ncard := by
  have h_union : f '' (Icc 1 2005) = f '' (Icc 1 1001) ∪ f '' (Icc 1002 2005) := by
    rw [← Set.image_union]
    suffices Icc 1 2005 = Icc 1 1001 ∪ Icc 1002 2005 by rw [this]
    rw [← Order.Ico_succ_right, ← Order.Ico_succ_right, ← Order.Ico_succ_right]
    simp
  rw [h_union]
  apply ncard_union_eq
  . rw [Set.disjoint_iff_forall_ne]
    -- disjoint as f is monotonic and f(1001) < f(1002)
    rintro a ha b hb
    simp [f] at ha hb
    obtain ⟨x, ⟨hx_lb, hx_ub⟩, hx⟩ := ha
    obtain ⟨y, ⟨hy_lb, hy_ub⟩, hy⟩ := hb
    rw [← hx, ← hy]
    have h1 := l_f_mono hx_ub
    have h2 := l_f_mono hy_lb
    simp [f] at h1 h2
    norm_num at h1 h2
    linarith
  . apply (finite_Icc _ _).image
  . apply (finite_Icc _ _).image

-- image of f on [1, 1001] is [0, 499]
lemma l_image_icc : f '' Icc 1 1001 = Icc 0 499 := by
  simp [Set.image]
  ext x; simp
  constructor
  -- if x in f ''[1, 1001]
  . rintro ⟨a, ⟨ha_lb, ha_ub⟩, ha⟩
    simp [← ha, f]
    and_intros
    -- by monotonicity of f, 0 ≤ x ≤ 499 as these are values at 1 and 1001
    . have h := l_f_mono ha_lb
      simp [f] at h
      norm_num at h
      assumption
    . have h := l_f_mono ha_ub
      simp [f] at h
      norm_num at h
      assumption
  -- if x is in [0, 499]
  . rintro ⟨hx_lb, hx_ub⟩
    -- then there is obviously x ≤ f(1001)  and 1 ≤ 1001
    have h_exists : ∃ b, 1 ≤ b ∧ x ≤ f b := by
      use 1001
      simp [f]
      norm_num
      assumption
    -- let n be smallest such value
    let n := Nat.find h_exists
    use n
    have hn1 : 1 ≤ n ∧ x ≤ f n := Nat.find_spec h_exists
    have hn2 : n ≤ 1001 := by
      apply Nat.find_min'
      simp [f]
      norm_num
      assumption
    and_intros
    -- the assumptions on n prove it is in 1, 1001
    . exact hn1.left
    . exact hn2
    -- if n = 1 then x must b 0
    . by_cases hn: n = 1
      . rw [hn, f] at hn1 ⊢
        norm_num at hn1 ⊢
        linarith
      -- othwerise f (n-1) ≤ x
      . replace hn : 2 ≤ n := by omega
        suffices f n < x + 1 by omega
        have h : ¬ (1 ≤ n - 1 ∧ x ≤ f (n - 1)) := Nat.find_min h_exists (show n - 1 < n by omega)
        simp at h
        specialize h (by omega)
        -- if x + 1 ≤ f(n) then diferent of terms inside floor for n and (n-1) are too small and contradiction
        by_contra h'
        simp at h'
        simp [f] at h h'
        rw [Int.le_floor] at h'
        rw [Int.floor_lt] at h
        push_cast [show 1 ≤ n by omega] at h h'
        have h'' : 1003 < (n : ℝ) := by linarith
        norm_cast at h''
        linarith

-- f is injective on (2002, 2005)
lemma l_f_inj_on : InjOn f (Icc 1002 2005) := by
  rintro a ha b hb hab
  -- wlog a ≤ b
  wlog h : a ≤ b
  . simp at h
    rw [this hb ha hab.symm h.le]
  -- as 1002 ≤ a, b
  simp [f] at hab ha hb
  rw [eq_comm] at hab
  -- floor equality means terms difference is < 1
  replace hab := Int.abs_sub_lt_one_of_floor_eq_floor hab
  -- but if a ≠ b, then a + 1 ≤ b and terms difference is > 1
  by_contra h'
  replace h : a + 1 ≤ b := by omega
  rify at h
  rw [← sq_le_sq₀ (by positivity) (by positivity)] at h
  rify at ha
  have : (1 : ℝ) ≤ b ^ 2 / 2005 - a ^ 2 / 2005  := by linarith
  rw [abs_lt] at hab
  linarith

theorem number_theory_225950 : Set.ncard {n | ∃ (k : ℕ), n = ⌊(k ^ 2 : ℝ) / 2005⌋ ∧ 1 ≤ k ∧ k ≤ 2005} =
    1504 := by
  -- convert problem to f's application on [1, 2005], then use lemma's to show 1504
  convert_to (f '' (Icc 1 2005)).ncard = 1504
  . congr
    simp [f, Set.image]
    ext x
    simp
    tauto
  rw [l_union, l_image_icc, Set.ncard_image_of_injOn l_f_inj_on]
  convert_to (Finset.Icc (0 : ℤ) 499 : Set ℤ).ncard + (Finset.Icc 1002 2005 : Set ℕ).ncard = 1504
  . simp
  rw [Set.ncard_coe_Finset, Set.ncard_coe_Finset]
  simp