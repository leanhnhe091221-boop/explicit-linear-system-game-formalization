module

public import ThomGame.Pictures.GluedPreimageFaces

/-!
# Equal recovered exterior edge sets reflect equal target edge sets

Both recovery and the left input map are actual injective port maps.
Their indexed correspondences reflect common ports before and after
smoothing. This is the injectivity needed when counting components,
independently of any choice of circuit representative or enumeration.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (B : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)
  {N : PortGraph P (B.frontierWord s) []}
  (d : ThomGame.Pictures.ClosedGluingReduction (B.regionGraph hEuler s).swapBoundary N)
  (X Y : d.graph.SimpleCircuit)
  (D E : (B.regionGraph hEuler s).swapBoundary.SimpleCircuit)
  (hD : D.length = X.length) (hE : E.length = Y.length)
  (hpD : ∀ x : Fin D.length × Bool,
    compLeftEmbedding (B.regionGraph hEuler s).swapBoundary N (D.port x) =
      d.trace.portEmbedding (X.port (finCongr hD x.1, x.2)))
  (hpE : ∀ x : Fin E.length × Bool,
    compLeftEmbedding (B.regionGraph hEuler s).swapBoundary N (E.port x) =
      d.trace.portEmbedding (Y.port (finCongr hE x.1, x.2)))

include hpD hpE in
theorem marked_imp_of_recovered_exterior
    (hm : ∀ x, (B.recoverSwappedRegionCircuit hEuler s D).Marked x →
      (B.recoverSwappedRegionCircuit hEuler s E).Marked x)
    (x : d.graph.Dart) (hx : X.Marked x) : Y.Marked x := by
  obtain ⟨⟨k, side⟩, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := (finCongr hD).surjective k
  have hsource : (B.recoverSwappedRegionCircuit hEuler s E).Marked
      ((B.recoverSwappedRegionCircuit hEuler s D).port (k, side)) := hm _ ⟨(k, side), rfl⟩
  obtain ⟨y, hy⟩ := hsource
  rw [B.recoverSwappedRegionCircuit_port, B.recoverSwappedRegionCircuit_port] at hy
  have he := (B.swappedRegionPortEmbedding hEuler s).injective hy
  refine ⟨(finCongr hE y.1, y.2), d.trace.portEmbedding.injective ?_⟩
  exact (hpE y).symm.trans ((congrArg (compLeftEmbedding (B.regionGraph hEuler s).swapBoundary N) he).trans
    (hpD (k, side)))

include hpD hpE in
theorem marked_iff_of_recovered_exterior
    (hm : ∀ x, (B.recoverSwappedRegionCircuit hEuler s D).Marked x ↔
      (B.recoverSwappedRegionCircuit hEuler s E).Marked x) :
    ∀ x, X.Marked x ↔ Y.Marked x := fun x =>
  ⟨B.marked_imp_of_recovered_exterior hEuler s d X Y D E hD hE hpD hpE (fun z => (hm z).mp) x,
    B.marked_imp_of_recovered_exterior hEuler s d Y X E D hE hD hpE hpD (fun z => (hm z).mpr) x⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit
