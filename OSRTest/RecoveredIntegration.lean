import OSR.IntegrationRecovered

open OSR OSR.Calculus OSR.IntegrationRecovered

#guard !entries.isEmpty
#guard entries.all (fun e => e.rule.conditionsOk && e.rule.recOk &&
  (e.rule.shape == .antiderivRec || e.rule.shape == .antiderivSubst || e.rule.wellFormed))
#guard entries.all (fun e => e.rule.legacyId.isSome)
#guard (entries.map (·.rule.legacyId)).eraseDups.length == entries.length
#guard (entries.map (·.rule.priority)).Pairwise (· < ·)

#guard entries.all (fun e => e.unproved.all (fun d =>
  e.rule.symbols.all (fun s => ((Registry.lookup s).bind (fun entry => entry.interpretations.find? (·.domain == d))).isSome)))
