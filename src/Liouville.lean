/-
In this file we will prove Liouville's Theorem in the usual form for irrational α in ℝ.
We will follow Zannier's "Lecture Notes on Diophantine Analysis" where the Liouville's Theorem is Theorem 2.3
-/
import field_theory.minpoly.is_integrally_closed
import data.real.irrational
import analysis.calculus.cont_diff
import data.polynomial.denoms_clearable
import data.polynomial.denoms_clearable
-- import analysis.calculus.mean_value
--MEAN VALUE THEOREM is
-- exists_has_deriv_at_eq_slope
-- LIOUVILLE IN MATHLIB
-- import number_theory.liouville.basic

-- import topology.algebra.ordered
-- EXTREME VALUE THEOREM (continuous function on compact obtains max)
-- is_compact.exists_forall_ge

noncomputable theory
open_locale polynomial 

-- notation `transcendental` x := ¬(is_algebraic ℤ x)


/- 
Servirebbe lemma che passa dal minpoly al polinomio in ℤ[X] primitivo di grado minimo che si annulla in x, per poter richimare il lemma qui sotto
  -/

/- 
Servirebbe lemma che passa dal minpoly al polinomio in ℤ[X] primitivo di grado minimo che si annulla in x, per poter richimare il lemma qui sotto
  -/

/-
 The Lemma gives a lower bound on the absolute value of a polynomial f with integral coefficients evaluated at a rational number x which is not a root of f 
 -/
lemma poly_not_zero_low_bound (a b : ℤ  ) (p : ℤ [X]) (hb : 0<b ) 
(hpab : polynomial.aeval (  (a: ℚ ) / (b  : ℚ  ) ) (polynomial.map (algebra_map ℤ ℚ ) p )≠ 0) :1 ≤ (↑b)^(p.nat_degree)* abs( polynomial.aeval (  (a: ℚ ) / (b  : ℚ  ) ) (polynomial.map (algebra_map ℤ ℚ ) p ))  :=
begin
  exact one_le_pow_mul_abs_eval_div hb hpab,
end

/-
lemma: minimal polynomial of an irrational does not have rational roots
-/
lemma rat_not_root_minpoly_irrat (y : ℚ) (x : ℝ) (hirr : irrational x) (hint: is_integral ℚ x): ¬ (polynomial.is_root (minpoly ℚ x) y):=
begin
  by_contradiction,
  -- minimal polynomial is prime
  have h_prime := minpoly.prime hint,
  -- irreducible polynomial with a root has degree 1
  have h_irr_one := polynomial.degree_eq_one_of_irreducible_of_root (h_prime.irreducible) h,
  -- x is a root of its minimal polynomial
  have h_x_root :=  minpoly.aeval ℚ x,
  -- if x is a root of a degree one polynomial with ℚ coefficients then x ∈ ℚ 
  have h_x_Q := minpoly.mem_range_of_degree_eq_one ℚ x h_irr_one,
  -- Lean is able to figure out the contraddicition using hirr
  tauto,
end

def const_Liouville {x : ℝ} (hint : is_integral ℚ x) : ℝ := 
  sorry

variables {x : ℝ} (hint: is_integral ℚ x) 

lemma const_Liouville_pos : const_Liouville (hint) > 0 :=
  sorry

-- Liouville Theorem
include hint
-- add the hint in the hypothesis using the fact that is included in ``variables'' above
theorem liouville (hirr : irrational x) :   ∀ a b : ℤ, b > 0 → abs(x - (a / b)) > (1 / b^(minpoly ℚ x).nat_degree) :=
begin
-- exact zero_lt_one
intros a b hb,
-- mai UNFOLD definition
-- usare aeval di solito invece che eval₂
-- p is minpoly 
unfold is_integral at hint,
rcases hint with ⟨p, hpmonic, hpzero⟩,
-- richimare lemma che "trasforma" p a coeff in ℤ di grado minimo
-- richimare lemma che "trasforma" p a coeff in ℤ di grado minimo
-- cases hp with hpmonic hpzero,
have h1 : abs((polynomial.eval₂ (algebra_map ℚ ℝ) x p) - (polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p)) = abs(polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p),
-- the absolute values are the same since x is a zero of its minimal polynomial
{
    -- have := minpoly.aeval ℚ x,
    rw hpzero,
    simp,
},

have hmeanval : ∃ α : ℝ,  (α < x ) ∧ ( α > (↑a / ↑b ) ) ∧ abs((polynomial.eval₂ (algebra_map ℚ ℝ) x p) - (polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p)) = abs (x - (↑ a / ↑ b )) * abs (polynomial.eval₂ (algebra_map ℚ ℝ) α (polynomial.derivative p)),
{
  sorry,
},

sorry,
end

