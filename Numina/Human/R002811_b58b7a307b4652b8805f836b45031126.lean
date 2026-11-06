import Mathlib

open Real Set
open scoped BigOperators

/- 7. Let the function $f(x)$ satisfy $f\left(2^{x}\right)=x^{2}-2 a x+a^{2}$ -1, and $f(x)$ has a range of $[-1,0]$ on the interval $\left[2^{a-1}, 2^{a^{2}-2 a+2}\right]$, then the range of values for $a$ is $\qquad$. -/

-- a lemma that the function's property is equivalent to g where g (x) = (x - a)^2 - 1
lemma l_equiv_function {a : ℝ} {f g : ℝ -> ℝ} (hf : ∀ x, f (2 ^ x) = x ^ 2 - 2 * a * x + a ^ 2 - 1)
    (hg : ∀ x, g x = (x - a) ^ 2 - 1) : f '' (Icc (2 ^ (a - 1)) (2 ^ (a ^ 2 - 2 * a + 2))) = Icc (-1) 0 ↔ g ''  (Icc (a - 1) (a ^ 2 - 2 * a + 2)) = Icc (-1) 0 := by
  suffices f '' Icc (2 ^ (a - 1)) (2 ^ (a ^ 2 - 2 * a + 2)) =  g ''  (Icc (a - 1) (a ^ 2 - 2 * a + 2)) by
    rw [this]
  ext v
  constructor <;> (rintro h; obtain ⟨x, h⟩ := h; simp at h; obtain ⟨⟨h_lb, h_ub⟩, h⟩ := h)
  -- use x ↦ logb 2 x to map from f to g
  . use logb 2 x
    have : 0 < x := by calc
      _ < 2 ^ (a - 1) := by positivity
      _ ≤ x := h_lb
    have hx : x = 2 ^ (logb 2 x) := by
      rw [Real.rpow_logb (show 0 < 2 by norm_num) (by norm_num) (by assumption)]
    conv_rhs => arg 2; rw [← h, hx, hf]
    conv_rhs => arg 1; rw [hg]
    conv_rhs => ring
    simp
    rw [hx] at h_lb h_ub
    and_intros
    . have := (Real.strictMono_rpow_of_base_gt_one (show 1 < (2 : ℝ) by norm_num)).le_iff_le |>.mp h_lb
      linarith
    . have := (Real.strictMono_rpow_of_base_gt_one (show 1 < (2 : ℝ) by norm_num)).le_iff_le |>.mp h_ub
      linarith
  -- use x → 2 ^ x to map from g to f
  . use 2 ^ x
    conv_rhs => arg 2; rw [← h, hg]
    conv_rhs => arg 1; rw [hf]
    conv_rhs => ring
    simp [h_lb, h_ub]

-- lemma for quadratic inequality
lemma l_sub_mul_sub_nonpos_iff (x : ℝ) (h : a ≤ b) :  (x - a) * (x - b) ≤ 0 ↔ a ≤ x ∧ x ≤ b := by
  rw [mul_nonpos_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos, or_iff_left_iff_imp, and_comm]
  exact And.imp h.trans h.trans'

-- lemma for quadratic inequality
lemma l_sub_mul_sub_nonneg_iff (x : ℝ) (h : a ≤ b) : 0 ≤ (x - a) * (x - b) ↔ x ≤ a ∨ b ≤ x := by
  rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos,
    and_iff_right_of_imp h.trans, and_iff_left_of_imp h.trans', or_comm]

-- the inequality of rhs is equivalent to two quadratic inequalities
lemma l_ineq (a : ℝ) : (3 - √5) / 2 ≤ a ∧ a ≤ 1 ∨ 2 ≤ a ∧ a ≤ (3 + √5) / 2 ↔
    ((a - 1) + (a^2 - 2 * a + 2))/2 ≤ a ∧ a ≤ a^2 - 2 * a + 2 := by
  have : (3 - √5) /2 ≤ 1 := by
    suffices 1 ≤ √5 by linarith
    simp
  have : 2 ≤ (3 + √5) /2 := by
    suffices 1 ≤ √5 by linarith
    simp
  -- first of all the inequalities are just requirement of belonging to an interval or not belongint to an interval, which translate to quadratic inequalities
  convert_to ((3 - √5)/2 ≤ a ∧ a ≤ (3 + √5)/2) ∧ (a ≤ 1 ∨ 2 ≤ a) ↔ _
  . constructor
    . rintro h
      obtain h | h := h
      . simp [h]
        linarith
      . simp [h]
        linarith
    . rintro ⟨h1, h2⟩
      obtain h2 | h2 := h2
      . left
        simp [h2]
        linarith
      . right
        simp [h2]
        linarith
  rw [← l_sub_mul_sub_nonpos_iff _ (by linarith), ← l_sub_mul_sub_nonneg_iff _ (by norm_num)]
  ring_nf
  simp
  constructor <;> (rintro h; and_intros <;> linarith)

-- for quadratic x → (x - a)^2 - 1, it's image of [b, c] is (-1, d) means b ≤ a and a ≤ c and max (f(b), f(c)) = d
lemma l_quadratic {a b c d: ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = (x - a) ^ 2 - 1) (hd: -1 ≤ d) :
    f '' (Icc b c) = Icc (-1) d ↔ b ≤ a ∧ a ≤ c ∧ max (f b) (f c) = d := by
  constructor <;> rintro h
  -- if image is true then -1 is only true at a, so a belongs to [b, c] and for any x in f(b, c) f(x) ≤ f(b) ⊔ f (c), so d ≤ f(b) ⊔ f(c). also since f(b), f(c) ∈ [-1, d], so f(b) ⊔ f(c) ≤ d
  . have hbc : b ≤ c := by
      by_contra h'
      simp [h'] at h
      rw [eq_comm, Set.Icc_eq_empty_iff] at h
      contradiction
    have h' := h
    simp [Set.image] at h
    have : -1 ∈ Icc (-1) d := by simp [hd]
    rw [← h] at this
    simp at this
    simp_rw [hf] at this
    simp at this
    obtain ⟨a', ⟨ha_lb, ha_ub⟩, ha⟩ := this
    replace ha : a' = a := by linarith
    rw [ha] at ha_ub ha_lb
    simp [ha_lb, ha_ub]
    apply le_antisymm
    . simp; and_intros
      . have : f b ∈ Icc (-1) d := by
          rw [← h']
          apply Set.mem_image_of_mem
          simp [hbc]
        simp at this
        linarith
      . have : f c ∈ Icc (-1) d := by
          rw [← h']
          apply Set.mem_image_of_mem
          simp [hbc]
        simp at this
        linarith
    . have : d ∈ Icc (-1) d := by simp [hd]
      rw [← h] at this
      simp at this
      obtain ⟨a', ⟨ha_lb, ha_ub⟩, ha⟩ := this
      obtain ha' | ha' := le_total a' a
      . have : f a' ≤ f b := by
          simp [hf]
          rw [← neg_sq, ← neg_sq (b - a)]
          rw [sq_le_sq₀ (by linarith) (by linarith)]
          linarith
        rw [ha] at this
        trans f b
        . assumption
        . simp
      . have : f a' ≤ f c := by
          simp [hf]
          rw [sq_le_sq₀ (by linarith) (by linarith)]
          linarith
        rw [ha] at this
        trans f c
        . assumption
        . simp
  -- if inequalities are true then, we can use a - √(x + 1) or a + √(x + 1) to show f(x) is in [-1, d]
  . obtain ⟨ha_lb, ha_ub, hbcd⟩ := h
    ext x
    simp
    constructor
    . rintro ⟨x, ⟨hx_lb, hx_ub, hx⟩⟩
      and_intros
      . rw [hf]
        linarith [show 0 ≤ (x - a)^2 by positivity]
      . obtain hx' | hx' := le_total x a
        . have : f x ≤ f b := by
            simp [hf]
            rw [← neg_sq, ← neg_sq (b -a), sq_le_sq₀ (by linarith) (by linarith)]
            linarith
          trans f b
          . assumption
          . simp [← hbcd]
        . have : f x ≤ f c := by
            simp [hf]
            rw [sq_le_sq₀ (by linarith) (by linarith)]
            linarith
          trans f c
          . assumption
          . simp [← hbcd]
    . rintro h
      obtain h' | h' := max_choice (f b) (f c)
      . rw [h'] at hbcd
        use a - √(x + 1)
        rw [hf]
        ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf; simp
        and_intros
        . suffices √(1 + x) ≤ a - b by linarith
          trans √(1 + f b)
          . gcongr; rw [hbcd]; linarith
          . rw [hf]
            simp
            rw [← neg_sq, sqrt_sq (by linarith)]
            linarith
        . have : 0 ≤ √(1 + x) := by positivity
          linarith
      . rw [h'] at hbcd
        use a + √(x + 1)
        rw [hf]
        ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf; simp
        and_intros
        . have : 0 ≤ √(1 + x) := by positivity
          linarith
        . suffices √(1 + x) ≤ c - a by linarith
          trans √(1 + f c)
          . gcongr; rw [hbcd]; linarith
          . rw [hf]
            simp
            rw [sqrt_sq (by linarith)]

theorem algebra_117159 {a : ℝ} (f : ℝ → ℝ)
    (h0 : ∀ x, f (2 ^ x) = x ^ 2 - 2 * a * x + a ^ 2 - 1) :
    f '' (Icc (2 ^ (a - 1)) (2 ^ (a ^ 2 - 2 * a + 2))) = Icc (-1) 0 ↔
    ((3 - √5) / 2 ≤ a ∧ a ≤ 1) ∨ (2 ≤ a ∧ a ≤ (3 + √5) / 2) := by
  -- define g and use lemma to change problem to g
  let g (x : ℝ) := (x - a) ^ 2 - 1
  rw [l_equiv_function h0 (g := g) (fun x ↦ by simp [g])]
  clear h0
  -- use inequality lemma to change rhs
  rw [l_ineq]
  have h1 : g a = -1 := by simp [g]
  have h2 : g (a - 1) = 0 := by simp [g]
  -- now use quadratic lemma to get simpler conditions, from which we get quadratic inequalities
  rw [l_quadratic (a := a) g (fun x ↦ by simp [g]) (by norm_num)]
  simp
  rw [and_comm]
  simp
  rintro h
  simp [h2]
  rw [← h2]
  simp [g]
  rw [abs_eq_self.mpr (by linarith)]
  constructor <;> (rintro h; linarith)