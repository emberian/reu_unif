use {Context, SigmaTerm, CapTerm};

pub struct Protocol {
    facts: Vec<SigmaTerm>,
    rules: Vec<ProtocolRule>,
}

pub struct ProtocolRule {
    pub left: Vec<SigmaTerm>,
    pub right: SigmaTerm,
}

impl Protocol {
    pub fn new(facts: Vec<SigmaTerm>, rules: Vec<ProtocolRule>) -> Protocol {
        Protocol {
            facts: facts,
            rules: rules,
        }
    }

    pub fn forward_search(&self, context: &Context, goal: SigmaTerm) -> (bool, CapTerm) {
        // TODO: Provide a trace
        let mut knowledge = CapTerm::Union(self.facts.iter().map(|x| x.to_cap().unwrap()).collect());
        // we use length of the knowledge as a proxy termination measure
        let mut old_len = knowledge.un().len();
        while context.match_(&goal, &knowledge).len() == 0 {
            for rule in &self.rules {
                for subst in context.match_(&SigmaTerm::Func(2, rule.left.clone()), &CapTerm::Func(2, knowledge.un().iter().cloned().cycle().take(rule.left.len()).collect())) {
                    knowledge.un().push(rule.right.subst(&subst).expect("subst was partial?"));
                }
            }
            knowledge.un().sort();
            knowledge.un().dedup();
            if knowledge.un().len() != old_len {
                old_len = knowledge.un().len();
            } else {
                return (false, knowledge);
            }
        }
        (true, knowledge)
    }
}
