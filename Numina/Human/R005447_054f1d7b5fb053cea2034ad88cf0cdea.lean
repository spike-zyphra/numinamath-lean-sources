import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

noncomputable section

-- volume of a square pyramid with square base of side s and height h
def squarePyramidVolume (s h : ℝ) : ℝ := (1 / 3) * s ^ 2 * h

-- volume of an octahedron made of two square pyramids with edge length 3
def octahedronVolume : ℝ :=
  let s := 3
  let h := (s * Real.sqrt 2) / 2
  2 * squarePyramidVolume s h

-- volume of one corner pyramid to remove (base square side 1, height √2 / 2)
def cornerVolume : ℝ := squarePyramidVolume 1 (sqrt 2 / 2)

-- total volume of truncated polyhedron
def polyhedronVolume : ℝ := octahedronVolume - 6 * cornerVolume

-- volume of region closest to one vertex
def targetVolume : ℝ := polyhedronVolume / 24

theorem truncated_octahedron_vertex_region_volume :
  targetVolume = sqrt 2 / 3 := by
  unfold targetVolume polyhedronVolume cornerVolume octahedronVolume squarePyramidVolume
  norm_num
  ring_nf
