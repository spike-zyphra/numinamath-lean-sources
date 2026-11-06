import Mathlib

theorem algebra_278984 {f g : ℝ → ℝ} :
    (Even f ∧ Even g ∨ Odd f ∧ Odd g) → Even (fun x => f x * g x) := by 
  intro h
  rcases h with (h | h)
  · -- Assume both functions are even
    rcases h with ⟨hf, hg⟩
    rcases hf with ⟨r, hfr⟩
    rcases hg with ⟨s, hsg⟩
    unfold Even 
    use 2 * (r * s)
    funext x
    -- Substitute the definitions
    have h1 : f x = r x + r x := by
      have h1 := congr_fun hfr x
      simpa using h1
    have h2 : g x = s x + s x := by
      have h2 := congr_fun hsg x
      simpa using h2
    -- Apply the substitutions
    simp [h1, h2]
    <;> ring
  · -- Assume both functions are odd
    rcases h with ⟨hf, hg⟩
    rcases hf with ⟨r, hfr⟩
    rcases hg with ⟨s, hsg⟩
    unfold Even
    use (fun x => (4 * r x * s x + 2 * r x + 2 * s x + 1) / 2)
    funext x
    -- Substitute the definitions
    have h1 : f x = 2 * r x + 1 := by
      have h1 := congr_fun hfr x
      simpa using h1
    have h2 : g x = 2 * s x + 1 := by
      have h2 := congr_fun hsg x
      simpa using h2
    -- Apply the substitutions
    simp [h1, h2]
    <;> ring_nf
    <;> try norm_num
    <;> try ring
    <;> try ring_nf
    <;> try norm_num
    <;> try ring_nf
    <;> try norm_num
    <;> try ring_nf
    <;> try norm_num
    <;> try ring_nf
    <;> try norm_num
    <;> try ring_nf