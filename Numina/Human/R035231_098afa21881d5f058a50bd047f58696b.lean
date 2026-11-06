import Mathlib
/- Soient $a, b, c$ trois nombres réels strictement positifs tels que $a+b+c=9$. Montrer que

$$
\frac{a^{3}+b^{3}}{a b+9}+\frac{b^{3}+c^{3}}{b c+9}+\frac{c^{3}+a^{3}}{c a+9} \geqslant 9
$$ -/
theorem inequalities_607602 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 9) :
    9 ≤ (a ^ 3 + b ^ 3) / (a * b + 9) + (b ^ 3 + c ^ 3) / (b * c + 9) + (c ^ 3 + a ^ 3) / (c * a + 9) := by
        -- Key lemma: For any positive x,y, proves (x³ + y³)/(xy + 9) ≥ x + y - 3
        have h1 : ∀ x y : ℝ, x > 0 → y > 0 → (x ^ 3 + y ^ 3) / (x * y + 9) ≥ x + y - 3:= by
            intro x y hx hy
            -- Step 1: Prove xy + 9 ≤ (x+y)²/4 + 9 using (x-y)² ≥ 0
            have h1 : x * y + 9 ≤ (x + y) ^ 2 / 4 + 9:= by
                have h1 : (x - y) ^ 2 ≥ 0:= by positivity
                linarith
            -- Step 2: Apply division inequality using previous result
            replace h1 : (x ^ 3 + y ^ 3) / (x * y + 9) ≥ (x ^ 3 + y ^ 3) / ((x + y) ^ 2 / 4 + 9):= by refine div_le_div_of_nonneg_left (by positivity) (by positivity) h1
            -- Step 3: Prove x³ + y³ ≥ (x+y)³/4 using (x+y)(x-y)² ≥ 0
            have h2 : x ^ 3 + y ^ 3 ≥ (x + y) ^ 3 / 4:= by
                have h2 : (x + y) * (x - y) ^ 2 ≥ 0:= by positivity
                linarith
            -- Step 4: Apply another division inequality
            replace h2 : (x ^ 3 + y ^ 3) / ((x + y) ^ 2 / 4 + 9) ≥ (x + y) ^ 3 / 4 / ((x + y) ^ 2 / 4 + 9):= by refine div_le_div_of_nonneg_right h2 (by positivity)
            -- Step 5: Final part of lemma, proving the inequality using substitution s = x + y
            have h3 : (x + y) ^ 3 / 4 / ((x + y) ^ 2 / 4 + 9) ≥ x + y - 3:= by
                have g1 : (x + y) ^ 2 / 4 + 9 > 0:= by positivity
                suffices (x + y) ^ 3 / 4 ≥ (x + y - 3) * ((x + y) ^ 2 / 4 + 9) by exact (le_div_iff₀ g1).mpr this
                set s:= x + y with hs
                clear_value s
                have h3 : (s - 6) ^ 2 ≥ 0:= by positivity
                linarith
            linarith
        -- Apply the lemma to each pair (a,b), (b,c), and (c,a)
        have h2:= h1 a b ha hb
        have h3:= h1 b c hb hc
        have h4:= h1 c a hc ha
        -- Combine the three inequalities using the fact that a + b + c = 9
        linarith
