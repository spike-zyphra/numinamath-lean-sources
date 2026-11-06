import Mathlib
/- Determine all real constants $t$ such that whenever $a, b, c$ are the lengths of the sides of a triangle, then so are $a^{2}+b c t, b^{2}+c a t, c^{2}+a b t$.

Proposed by S. Khan, UNK
The answer is the interval $[2 / 3,2]$. -/
theorem algebra_604344 (t : ℝ) : (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b > c → b + c > a → c + a > b →
a ^ 2 + b * c * t > 0 ∧ b ^ 2 + c * a * t > 0 ∧ c ^ 2 + a * b * t > 0 ∧ a ^ 2 + b * c * t + b ^ 2 + c * a * t > c ^ 2 + a * b * t ∧ b ^ 2 + c * a * t + c ^ 2 + a * b * t > a ^ 2 + b * c * t ∧ c ^ 2 + a * b * t + a ^ 2 + b * c * t > b ^ 2 + c * a * t) ↔
t ∈ Set.Icc (2 / 3) 2:= by
  constructor
  -- Forward direction: if the condition holds for all triangles, then t ∈ [2/3, 2]
  .
    intro h
    simp
    -- First prove that t ≤ 2
    have h1 : t ≤ 2:= by
      -- Proof by contradiction: assume t > 2
      by_contra H
      simp at H
      -- If t > 2, then t - 2 > 0
      have H1 : t - 2 > 0:= by linarith
      -- Define e = (t - 2) / (2 * t)
      set e:= (t - 2) / (2 * t) with he
      clear_value e
      -- Show that e > 0
      replace H1 : e > 0:= by
        subst e
        positivity
      -- Show that e < 2
      have H2 : e < 2:= by
        subst e
        replace H : 2 * t > 0:= by linarith
        suffices t - 2 < (2 * t) * 2 by exact (div_lt_iff₀' H).mpr this
        linarith
      -- Apply the hypothesis to the triangle with sides e, 1, 1
      specialize h e 1 1 H1 (by simp) (by simp) (by linarith) (by linarith) (by linarith)
      rcases h with ⟨_, _, _, h1, h2, h3⟩
      simp at h1 h2 h3
      ring_nf at h2
      -- Simplify the expression e * t * 2 = t - 2
      rw [show e * t * 2 = t - 2 by subst e ; field_simp ; ring_nf] at h2
      -- Since e² ≥ 0, we get a contradiction
      have h4 : e ^ 2 ≥ 0:= by positivity
      linarith
    refine ⟨?_, h1⟩
    -- Now prove that t ≥ 2/3
    by_contra H
    simp at H
    -- Define e = 3/8 * (2/3 - t)
    set e:= 3 / 8 * (2 / 3 - t) with he
    clear_value e
    -- Show that e > 0 (since t < 2/3)
    have H1 : e > 0:= by
      subst e
      linarith
    -- First show that t ≥ 0
    have h2 : t ≥ 0:= by
      -- Proof by contradiction: assume t < 0
      by_contra H
      simp at H
      -- Define s = min(-t, 1)
      set s:= min (-t) 1 with hs
      clear_value s
      -- Show that s > 0
      have hspos : s > 0:= by
        subst s
        replace H : -t > 0:= by linarith
        positivity
      -- Show that √(s/2) > 0
      have g : √(s / 2) > 0:= by positivity
      -- Show that √(s/2) < 2
      have g1 : √(s / 2) < 2:= by
        rw [show √(s / 2) = |√(s / 2)| by exact Eq.symm (abs_of_pos g)]
        rw [show (2 : ℝ) = |2| by simp]
        rw [show s / |2| = s / 2 by simp]
        suffices √(s / 2) ^ 2 < 2 ^ 2 by exact sq_lt_sq.mp this
        field_simp
        have g1 : s ≤ 1:= by subst s ; exact min_le_right (-t) 1
        linarith
      -- Apply the hypothesis to the triangle with sides √(s/2), 1, 1
      specialize h (√(s / 2)) 1 1 (by positivity) (by simp) (by linarith) (by linarith) (by linarith) (by linarith)
      replace h:= h.1
      field_simp at h
      -- Get a contradiction using the fact that s ≤ -t
      have h2 : s ≤ -t:= by subst s ; exact min_le_left (-t) 1
      linarith
    -- Apply the hypothesis to the triangle with sides 2, 1+e, 1+e
    specialize h 2 (1 + e) (1 + e) (by simp) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    replace h:= h.2.2.2.2.1
    -- Show that the triangle inequality leads to a contradiction
    suffices 1 / 4 * (2 - t) * e * (e + 2) + e * t ≤ 2 * e by linarith
    replace h1 : 2 - t ≥ 0:= by linarith
    have h3 : e + 2 ≤ 4:= by
      subst e
      linarith
    replace h1 : 1 / 4 * (2 - t) * e ≥ 0:= by positivity
    replace h1 : 1 / 4 * (2 - t) * e * (e + 2) ≤ 1 / 4 * (2 - t) * e * 4:= by exact mul_le_mul_of_nonneg_left h3 h1
    linarith
  -- Backward direction: if t ∈ [2/3, 2], then the condition holds for all triangles
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    intro a b c ha hb hc hab hbc hca
    -- Prove the main lemma: for any triangle inequality holds for the transformed sides
    have h3 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b > c → b + c > a → c + a > b → a ^ 2 + b * c * t + b ^ 2 + c * a * t > c ^ 2 + a * b * t:= by
      intro a b c ha hb hc hab hbc hca
      -- Use the fact that (2 + t) * (a - b)² ≥ 0
      have g1 : (2 + t) * (a - b) ^ 2 ≥ 0:= by positivity
      -- The main inequality can be rewritten as a quadratic form
      suffices 1 / 4 * (2 - t) * (a + b) ^ 2 + c * t * (a + b) - c ^ 2 > 0 by linarith
      replace h2 : 1 / 4 * (2 - t) ≥ 0:= by linarith
      have h3 : c * t > 0:= by positivity
      -- Use the triangle inequality a + b > c
      replace h3 : c * t * (a + b) > c * t * c:= by exact (mul_lt_mul_left h3).mpr hab
      -- Convert to squared form
      rw [show a + b = |a + b| by exact Eq.symm (abs_of_pos (by linarith))] at hab
      rw [show c = |c| by exact Eq.symm (abs_of_pos (by linarith))] at hab
      replace hab : (a + b) ^ 2 > c ^ 2:= by exact sq_lt_sq.mpr hab
      replace hab : (a + b) ^ 2 ≥ c ^ 2:= by linarith
      replace h2 : 1 / 4 * (2 - t) * (a + b) ^ 2 ≥ 1 / 4 * (2 - t) * c ^ 2:= by exact mul_le_mul_of_nonneg_left hab h2
      -- The final step uses the fact that t ≥ 2/3
      suffices (t - 2 / 3) * c ^ 2 ≥ 0 by linarith
      replace h1 : t - 2 / 3 ≥ 0:= by linarith
      positivity
    -- Apply the lemma to all three triangle inequalities
    refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
    -- First triangle inequality: a² + bct + b² + cat > c² + abt
    .
      linarith only [h3 a b c ha hb hc hab hbc hca]
    -- Second triangle inequality: b² + cat + c² + abt > a² + bct
    .
      linarith only [h3 b c a hb hc ha (by linarith) (by linarith) (by linarith)]
    -- Third triangle inequality: c² + abt + a² + bct > b² + cat
    .
      linarith only [h3 c a b hc ha hb (by linarith) (by linarith) (by linarith)]
