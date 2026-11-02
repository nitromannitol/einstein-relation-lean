import EinsteinFull.External.Draft.AKMLocalizedEnergy

namespace EinsteinFull.External

/-- AKM (5.85), with the genuine finite-domain coordinate minimizers of
pp.155–156 and variational energy (4.103). This is the reviewed r≥2 source
specialization. Stationary/horizontal and joint-clock applications remain
internal; no arbitrary localized energy is admitted. -/
axiom akm_localized_energy : EinsteinFull.External.Draft.akmLocalizedEnergyStmt

end EinsteinFull.External
