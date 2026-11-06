import Mathlib
open Mathlib
namespace algebra_328194
theorem discrim_eq_zero_of_existsUnique {a b c : ℝ} (ha : a ≠ 0) (h : ∃! x, a * (x * x) + b * x + c = 0) :
    discrim a b c = 0 := by
  simp_rw [quadratic_eq_zero_iff_discrim_eq_sq ha] at h
  generalize discrim a b c = d at h
  obtain ⟨x, rfl, hx⟩ := h
  specialize hx (-(x + b / a))
  field_simp [ha] at hx
  specialize hx (by ring)
  linear_combination -(2 * a * x + b) * hx
end algebra_328194
/--
Example 4 Let $a$ be a real number greater than zero. It is known that there exists a unique real number $k$, such that the quadratic equation in $x$
$$
x^{2}+\left(k^{2}+a k\right) x+1999+k^{2}+a k=0
$$

has two roots that are both prime numbers. Find the value of $a$.
(1999, National Junior High School Mathematics Competition)
-/
theorem algebra_328194 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ → ℝ) (hf : ∀ x k, f x k = x * x + (k * k + a * k) * x + 1999 + k * k + a * k) (he : ∃! (k : ℝ), ∃ (p q : ℕ), p ≠ q ∧ Nat.Prime p ∧ Nat.Prime q ∧ f ↑p k = 0 ∧ f ↑q k = 0) : a = 2 * √502 := by
  obtain ⟨k, ⟨⟨p, q, dn, pp, pq, ep, eq⟩, hl⟩⟩ := he
  simp only [exists_and_left, forall_exists_index, and_imp] at hl
  -- By the relationship between roots and coefficients, we have $$ \begin{array}{l} p+q=-k^{2}-a k, \ p q=1999+k^{2}+a k .
  simp only [hf] at ep
  simp only [hf] at eq
  obtain ⟨y, y1, y2⟩ := vieta_formula_quadratic (b := -(k * k + a * k)) (c := 1999 + k * k + a * k) (x := ↑p) (by linarith)
  have stk := (quadratic_eq_zero_iff_discrim_eq_sq (a := 1) (b := (k * k + a * k)) (c := 1999 + k * k + a * k) (x := ↑p) (by linarith)).mp (by linarith)
  rw [pow_two] at stk
  have ma := quadratic_eq_zero_iff (a := 1) (b := (k * k + a * k)) (c := 1999 + k * k + a * k) (by norm_num) stk
  -- now we do some magic to make y = p ∨ y = q
  have ap1 := (ma p).mp (by linarith)
  have ap2 := (ma q).mp (by linarith)
  have ap3 := (ma y).mp (by linarith)

  have desired : y = p ∨ y = q := by
    obtain a1 | a1 := ap1
    all_goals obtain a2 | a2 := ap2
    all_goals obtain a3 | a3 := ap3
    all_goals try (left; linarith)
    all_goals try (right; linarith)
    all_goals have wla : (↑p : ℝ) ≠ (↑q : ℝ) := by norm_cast
    all_goals rw [a1, a2] at wla
    all_goals exact (False.elim (wla rfl))
  
  -- let's forget what q is, we have y already
  -- we get what we want from y
  -- then delete q for good

  -- we create an intermediate natural number
  obtain ⟨i, hi⟩: ∃ (i : ℕ), y = ↑i := by
    obtain ja | ja := desired
    all_goals rw [ja]
    · exists p
    · exists q
  -- we don't need y anymore
  subst y
  norm_cast at desired

  -- now we need function application
  have fa : f ↑i k = 0 := by
    simp only [hf]
    obtain rfl | rfl := desired
    all_goals tauto

  -- then we need primality
  have pr : Nat.Prime i := by
    obtain rfl | rfl := desired
    all_goals tauto
  
  -- now we can delete q for good
  clear eq pq dn ap2 desired q

  -- Adding (1) and (2) gives } p+q+p q=1999, \text { i.e., } \ (p+1)(q+1)=2^{4} \times 5^{3}
  obtain ⟨y3, y4⟩ := y2
  have prd : (p + 1) * (i + 1) = 2000 := by ring_nf; rify; linarith

  -- solve this beforehand, it will be of use later
  -- n1 and n2 are conditions that are always satisfied when substituted with concrete values
  have slv (hh : k * k + a * k + 502 = 0) (hd : p ≠ i) (n1 : 1497 - (↑p : ℝ) * 502 + (↑p : ℝ) ^ 2 = 0) (n2 : 1497 - (↑i : ℝ) * 502 + (↑i : ℝ) ^ 2 = 0) : a = 2 * √502 := by
    have jn := fun mm => hl mm p i hd pp pr
    -- k must be unique
    have nq : ∀ x, x * x + a * x + 502 = 0 → x = k := by
      intros x hx
      have pog : f p x = 0 := by
        simp only [hf]
        simp only [(by clear * - hx; linarith : x * x + a * x = -502)]
        ring_nf
        rw [(by linarith : 1999 - ↑p * 502 + ↑p ^ 2 + x * a + x ^ 2 = 1497 - ↑p * 502 + ↑p ^ 2)]
        exact n1
      have pag : f i x = 0 := by
        simp only [hf]
        simp only [(by clear * - hx; linarith : x * x + a * x = -502)]
        ring_nf
        rw [(by linarith : 1999 - ↑i * 502 + ↑i ^ 2 + x * a + x ^ 2 = 1497 - ↑i * 502 + ↑i ^ 2)]
        exact n2
      have sl := jn x pog pag
      exact sl
    have md : ∃! x, 1 * (x * x) + a * x + 502 = 0 := by
      exists k
      simp only [one_mul]
      constructor
      · linarith
      · exact nq
    -- now we calculate the discriminant of the equation
    have kx := algebra_328194.discrim_eq_zero_of_existsUnique (a := 1) (b := a) (c := 502) (by norm_num) md
    simp only [discrim] at kx
    have di : a^2 = (2^2) * 502 := by clear * - kx; linarith
    apply_fun (fun x => √x) at di
    -- discriminant is 0, we solve for a
    rw [Real.sqrt_sq (by linarith), Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at di
    exact di
  
  -- now we already have the product of two natural numbers, we can just find divisors
  have nga : p + 1 ∈ (2000).divisors := by simp; use i + 1; rw [prd]
  simp only [show
      (2000 : ℕ).divisors =
        { 1, 2, 4, 5, 8, 10, 16, 20, 25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 1000, 2000 }
      from by native_decide,
    Finset.mem_insert, Nat.add_eq_right, Nat.reduceEqDiff, Finset.mem_singleton] at nga
  have md : i + 1 = 2000 / (p + 1) := by
    have nz : 0 < p + 1 := by norm_num
    rw [←prd, mul_comm, Nat.mul_div_left _ nz]
  have me : i = 2000 / (p + 1) - 1 := by clear * - md; omega
  clear md
  rcases nga with nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga | nga
  -- eliminate all solutions that are not prime
  all_goals subst p
  all_goals norm_num at pp
  all_goals norm_num at me
  all_goals subst i
  all_goals norm_num at pr
  -- now we continue
  -- we end up with (3, 499) and (499, 3). these goals will be solved together
  all_goals exact slv (by clear * - y4; norm_num at y4; linarith : k * k + a * k + 502 = 0) (by norm_num) (by norm_num) (by norm_num)