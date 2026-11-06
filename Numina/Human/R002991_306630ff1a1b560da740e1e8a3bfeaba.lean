import Mathlib

/- (6) In the geometric sequence $\left\{a_{n}\right\}$ with all terms being positive, $2 a_{4}+a_{3}-2 a_{2}-a_{1}=8$, then the minimum value of $2 a_{8}+a_{7}$ is $\qquad$. -/

-- in geoemteric series terms except the first can be written in terms of 2nd element
lemma l_geom {a : ℕ → ℝ} {r : ℝ} (h : ∀ n, a n = a 0 * r ^ n) (n : ℕ) (hn : n > 0) :
    a n = a 1 * r ^ (n - 1) := by
  rw [h n, h 1]
  ring_nf
  rw [mul_assoc, mul_comm r,  ← pow_succ]
  rw [show n - 1 + 1 = n by omega]

-- in given target, 2 * a 3 + a 2 - 2 * a 1 - a 0 = 8 can be turned into a more easier to work with state by writing a 3 in terms of a 1 and a 2 in temrs of a 0
lemma lemma_2 {a : ℕ → ℝ} {r : ℝ} (h : ∀ n, a n = a 0 * r ^ n) : 2 * a 3 + a 2 - 2 * a 1 - a 0 = 8 ↔
    (2 * a 1 + a 0) = 8 / (r^2 - 1) ∧ (r^2 - 1 ≠ 0) := by
  rw [l_geom h 3 (by norm_num), h 2]
  calc
    _ ↔ (2 * a 1 + a 0) * (r^2 - 1) = 8 := by ring_nf
    _ ↔ (2 * a 1 + a 0) = 8 / (r^2 - 1) ∧ (r^2 - 1) ≠ 0 := by
      by_cases h' : r^2 - 1 ≠ 0
      . simp [h']
        field_simp
      . simp at h'
        rw [h']
        simp

-- target expression can be written in terms of a 0 and a 1 to get something related to last lemma
lemma lemma_3 {a : ℕ → ℝ} {r : ℝ} (h : ∀ n, a n = a 0 * r ^ n) : 2 * a 7 + a 6 = (2 * a 1 + a 0) * r^6 := by
  rw [h 6, l_geom h 7 (by norm_num)]
  ring_nf

-- the function (fun (x : ℝ) ↦ 24 + x * 24 + x ^ 2 * 8 + x⁻¹ * 8) is used in the proof, we prove that on (0, ∞) it is differentiable an it's derivative is negative on (0, 1/2) but positive on (1/2, ∞), hence decreasing then increasing
lemma lemma_4 : AntitoneOn (fun (x : ℝ) ↦ 24 + x * 24 + x ^ 2 * 8 + x⁻¹ * 8) (Set.Ioc 0 (1/2)) ∧
    MonotoneOn (fun (x : ℝ) ↦ 24 + x * 24 + x ^ 2 * 8 + x⁻¹ * 8) (Set.Ici (1/2)) := by
  let f := (fun (x : ℝ) ↦ 24 + x * 24 + x ^ 2 * 8 + x⁻¹ * 8)
  have hd (x : ℝ) (hx : x ≠ 0) : deriv f x = 8 * (x + 1)^2 * (2 * x - 1) / x^2 := by
    simp [f]
    rw [deriv_add (by fun_prop) (by fun_prop (disch := assumption))]
    rw [deriv_add (by fun_prop) (by fun_prop)]
    rw [deriv_add (by fun_prop) (by fun_prop)]
    simp
    field_simp
    ring
  and_intros
  -- proving decreasing
  . apply antitoneOn_of_deriv_nonpos
    . exact convex_Ioc 0 (1 / 2)
    . have (x : ℝ) (hx : x ∈ Set.Ioc 0 (1/2)) : x ≠ 0 := by simp at hx; linarith
      fun_prop (disch := assumption)
    . simp
      have (x : ℝ) (hx : x ∈ Set.Ioo 0 2⁻¹) : x ≠ 0 := by simp at hx; linarith
      fun_prop (disch := assumption)
    . rintro x hx
      simp at hx
      rw [hd x (by linarith)]
      suffices 0 ≤ 8 * (x + 1) ^ 2 * (1 - 2 * x) / x ^ 2 by linear_combination this
      have : 0 ≤ 1 - 2 * x := by linarith
      positivity
  -- proving increasing
  . apply monotoneOn_of_deriv_nonneg
    . exact convex_Ici (1 / 2)
    . have (x : ℝ) (hx : x ∈ Set.Ici (1/2)) : x ≠ 0 := by simp at hx; linarith
      fun_prop (disch := assumption)
    . simp
      have (x : ℝ) (hx : x ∈ Set.Ioi 2⁻¹) : x ≠ 0 := by simp at hx; linarith
      fun_prop (disch := assumption)
    . rintro x hx
      simp at hx
      rw [hd x (by linarith)]
      have : 0 ≤ 2 * x - 1 := by linarith
      positivity

theorem algebra_140304 :
    IsLeast {(2 * a 7 + a 6) | (a : ℕ → ℝ) (r : ℝ) (_ : ∀ n, a n = a 0 * r ^ n) (_ : ∀ n, 0 < a n)
    (_ : 2 * a 3 + a 2 - 2 * a 1 - a 0 = 8)} 54 := by
  -- statement has been changed to easier to work form by shifting indexes one step down
  -- using the lemmas we convert hypothesis to easier form
  convert_to IsLeast {(2 * a 1 + a 0) * r^6 | (a : ℕ → ℝ) (r : ℝ) (_ : ∀ n, a n = a 0 * r ^ n)
      (_ : ∀ n, 0 < a n) (_ : (2 * a 1 + a 0) = 8 / (r^2 - 1)) (_ : r^2 - 1 ≠ 0)} 54
  . ext x
    apply exists_congr
    rintro a
    apply exists_congr
    rintro r
    apply exists_congr
    rintro h
    apply exists_congr
    rintro ha_pos
    simp
    rw [lemma_2 h, lemma_3 h]
    tauto
  constructor
  -- to prove 54 is attianable use geometric series with first term (√6 - 1) * 16 / 5 and common ration √6 / 2
  . simp
    use fun i ↦ (√6 - 1) * 16 / 5 * (√6 / 2) ^ i, √6 / 2
    and_intros
    . ring_nf; simp; norm_num
    . ring_nf; simp; norm_num
    . rintro n
      have : 0 < √6 - 1 := by
        rw [sub_pos, show 1 = √1 by norm_num, Real.sqrt_lt_sqrt_iff (by norm_num)]
        norm_num
      positivity
    . ring_nf; simp
    . ring_nf
      rw [show 8 = 2 * 4 by norm_num, show 6 = 2 * 3 by norm_num, pow_mul, pow_mul]
      simp
      norm_num
  -- to show 54 is a lower bound
  . rintro x ⟨a, r, h, ha_pos, h', hr, hx⟩
    rw [← hx]
    clear x hx
    -- prove r^2  - 1 > 0 as it's not 0 but if it was less than 0 then two sides of 2 * a 1 + a 0 = 8 / (r ^ 2 - 1) have different signs
    replace hr : 0 < r^2 - 1 := by
      by_contra hr'
      simp only [not_lt] at hr'
      replace hr' := hr'.lt_of_ne hr
      have : 0 < 2 * a 1 + a 0 := by linarith [ha_pos 0, ha_pos 1]
      have : 8 / (r ^ 2 - 1) < 0 := div_neg_of_pos_of_neg (by norm_num) hr'
      linarith
    rw [h']
    clear h'
    -- replace r^2 - 1 by t on (0, ∞ )
    rw [show r ^ 6 = (r ^ 2 - 1 + 1)^3 by ring]
    set t := r^2 - 1 with ht
    -- we get that target is f (1/2) ≤ f (t), function from lemma
    let f (t : ℝ) := 24 + t * 24 + t ^ 2 * 8 + t⁻¹ * 8
    convert_to f (1 / 2) ≤ f t
    . simp [f]; norm_num
    . simp [f]
      field_simp
      ring
    -- then it is decreasing upto 1/2 then increasing, so f (t) always greater than or equal to f(1/2)
    obtain ⟨hf1, hf2⟩ := lemma_4
    obtain ht | ht := le_total t (1/2)
    . apply hf1
      . simp at ht ⊢; simp [ht]; assumption
      . simp
      . assumption
    . apply hf2
      . simp
      . simp at ht ⊢; simp [ht]
      . assumption