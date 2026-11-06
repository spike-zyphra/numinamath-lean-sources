import Mathlib

/- Consider this pattern where the positive, proper fractions with denominator $(n+1)$  are arranged in the $n$th row in a triangular formation. The 1st through 4th rows are shown; each row has one more entry than the previous row. What is the sum of the fractions in the 15th row?

[asy]
label("$\frac{1}{2}$",(0,0),S);
label("$\frac{1}{3}$",(-5,-5),S);
label("$\frac{2}{3}$",(5,-5),S);
label("$\frac{1}{4}$",(-10,-10),S);
label("$\frac{2}{4}$",(0,-10),S);
label("$\frac{3}{4}$",(10,-10),S);
label("$\frac{1}{5}$",(-15,-15),S);
label("$\frac{2}{5}$",(-5,-15),S);
label("$\frac{3}{5}$",(5,-15),S);
label("$\frac{4}{5}$",(15,-15),S);
dot((0,-22));
dot((0,-20));
dot((0,-24));
[/asy] -/
theorem algebra_18951 {n : ℕ} (hn : n = 15) :
    ∑ i ∈ Finset.range n, (i + 1 : ℚ) / (n + 1) = 15 / 2 := by
        -- 证明引理 ： ∑ i ∈ Finset.range k, (i + 1) = (k + 1) * k / 2
        have h1 : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i + 1 : ℚ) = ((↑k : ℚ) + 1) * k / 2:= by
            intro k
            induction k with
            | zero =>
                simp
            | succ k ih =>
                rw [Finset.range_succ]
                simp
                rw [ih]
                field_simp
                ring_nf
        specialize h1 n
        -- 将 1 / (n + 1) 提到外边
        have h2 : ∀ i : ℕ, ((↑i : ℚ) + 1) / (↑n + 1) = ((↑i : ℚ) + 1) * (1 / (↑n + 1)):= by
            intro i
            ring
        simp [h2]
        have h3 : ∑ i ∈ Finset.range n, ((↑i : ℚ) + 1) * ((↑n : ℚ) + 1)⁻¹ = (∑ i ∈ Finset.range n, ((↑i : ℚ) + 1)) * ((↑n : ℚ) + 1)⁻¹:= Eq.symm (Finset.sum_mul (Finset.range n) (fun i => (↑i : ℚ) + 1) (↑n + 1)⁻¹)
        rw [h3, h1]
        rw [hn]
        norm_num
