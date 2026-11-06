import Mathlib

/- Let $p, q, r$ be positive real numbers and $n \in \mathbb{N}$. Show that if $p q r=1$, then

$$
\frac{1}{p^{n}+q^{n}+1}+\frac{1}{q^{n}+r^{n}+1}+\frac{1}{r^{n}+p^{n}+1} \leq 1
$$ -/
theorem inequalities_239347 (p q r : ℝ) (hpos : p > 0 ∧ q > 0 ∧ r > 0)
    (n : ℕ) (hpqr : p * q * r = 1) :
    1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) +
    1 / (r ^ n + p ^ n + 1) ≤ 1 := by
  
  obtain ⟨hp, hq, hr⟩ := hpos

  -- The key idea is to deal with the case $n=3$.
  suffices (a b c : ℝ) : 0 < a → 0 < b → 0 < c → a * b * c = 1 →
    1 / (a ^ 3 + b ^ 3 + 1) +
    1 / (b ^ 3 + c ^ 3 + 1) +
    1 / (c ^ 3 + a ^ 3 + 1) ≤ 1
  
  -- Put $a=p^{n / 3}, b=q^{n / 3}$, and $c=r^{n / 3}$, 
  . let a := p ^ (n / 3 : ℝ)
    let b := q ^ (n / 3 : ℝ)
    let c := r ^ (n / 3 : ℝ)

    -- so $a b c=(p q r)^{n / 3}=1$ 
    have habc : a * b * c = 1 := by
      simp [a, b, c]
      rw [← Real.mul_rpow, ← Real.mul_rpow, hpqr, Real.one_rpow]
      <;> positivity
    
    -- $a ^ 3 = p ^ (n / 3) ^ 3 = p ^ 3$, similar for b, c
    have heq : a ^ (3 : ℝ) = p ^ n ∧ b ^ (3 : ℝ) = q ^ n ∧ c ^ (3 : ℝ) = r ^ n := by
      constructor <;> try constructor
      all_goals
        dsimp [a, b, c]
        rw [← Real.rpow_mul (le_of_lt (by assumption)), div_mul_cancel₀ _ three_ne_zero]
        norm_cast

    -- by applying the assumption, we can prove the desired inequality.
    specialize this a b c (by apply Real.rpow_pos_of_pos hp)  (by apply Real.rpow_pos_of_pos hq)  (by apply Real.rpow_pos_of_pos hr) habc
    norm_cast at heq
    convert this using 1
    simp [heq]

  -- now we need to show that when $n=3$ $$\frac{1}{p^3+q^3+1}+\frac{1}{q^3+r^3+1}+\frac{1}{r^3+p^3+1}\leq 1.$$

  -- Since $a b=c^{-1}$, $$ \frac{1}{a^{3}+b^{3}+1} \leq \frac{1}{(a+b) a b+1}=\frac{c}{a+b+c} $$, similarly for the 2 remaining terms.
  have t0 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (hprod : a * b * c = 1) :
      1 / (a ^ 3 + b ^ 3 + 1) ≤ c / (a + b + c) := by
    calc
    _ = 1 / ((a + b) * ((a - b) ^ 2 + a * b) + 1) := by
      congr
      ring
    _ ≤ 1 / ((a + b) * a * b + 1) := by
      apply one_div_le_one_div_of_le
      . positivity
      nlinarith
    _ = c / (a + b + c) := by
      field_simp
      nlinarith
  
  intros ha hb hc hprod
  have t1 := t0 a b c ha hb hc hprod
  have t2 := t0 b c a hb hc ha (by convert hprod using 1; ring)
  have t3 := t0 c a b hc ha hb (by convert hprod using 1; ring)
  
  -- Hence $$ \frac{1}{a^{3}+b^{3}+1}+\frac{1}{b^{3}+c^{3}+1}+\frac{1}{c^{3}+a^{3}+1} \leq \frac{c}{a+b+c}+\frac{a}{a+b+c}+\frac{b}{a+b+c}=1, $$
  calc
  _ ≤ c / (a + b + c) + a / (a + b + c) + b / (a + b + c) := by
    linear_combination t1 + t2 + t3
  _ = 1 := by
    field_simp
    ring
