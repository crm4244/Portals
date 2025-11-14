import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic


open Topology


class SideSpaceMaker {X : Type} [hX : TopologicalSpace X] (S : Set X) where
  Sides : Type
  topologicalSpace_type : TopologicalSpace Sides
  center : Sides → X
  touching_component : Sides → {connectedComponent p | p : X}


theorem ___ : {X : Type} → [TopologicalSpace X] → SideSpaceMaker


class PortalMap {X : Type} [TopologicalSpace X] {U : Set X} (f : U → X) where
  isOpen_domain : IsOpen U
  isOpenEmbedding : IsOpenEmbedding f


theorem
