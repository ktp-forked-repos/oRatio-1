package it.cnr.istc.oratio.timelines;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import it.cnr.istc.oratio.riddle.Atom;
import it.cnr.istc.oratio.riddle.InfRational;
import it.cnr.istc.oratio.riddle.Item;

/**
 * StateVariable
 */
public class StateVariable implements Timeline<StateVariable.SVValue> {

    public static TimelineBuilder BUILDER = new StateVariableBuilder();

    private final InfRational origin, horizon;
    private final List<SVValue> values = new ArrayList<>();

    private StateVariable(final InfRational origin, final InfRational horizon) {
        this.origin = origin;
        this.horizon = horizon;
    }

    /**
     * @return the origin
     */
    @Override
    public InfRational getOrigin() {
        return origin;
    }

    /**
     * @return the horizon
     */
    @Override
    public InfRational getHorizon() {
        return horizon;
    }

    private void addValue(final InfRational from, final InfRational to, final Collection<Atom> atoms) {
        values.add(new SVValue(from, to, atoms));
    }

    @Override
    public List<SVValue> getValues() {
        return Collections.unmodifiableList(values);
    }

    public class SVValue implements TimelineValue {

        private final InfRational from, to;
        private final Collection<Atom> atoms;

        private SVValue(final InfRational from, final InfRational to, final Collection<Atom> atoms) {
            this.from = from;
            this.to = to;
            this.atoms = atoms;
        }

        @Override
        public InfRational getFrom() {
            return from;
        }

        @Override
        public InfRational getTo() {
            return to;
        }

        /**
         * @return the atoms
         */
        public Collection<Atom> getAtoms() {
            return Collections.unmodifiableCollection(atoms);
        }
    }

    private static class StateVariableBuilder implements TimelineBuilder {

        @Override
        public StateVariable build(Item itm, Collection<Atom> atoms) {
            StateVariable sv = new StateVariable(((Item.ArithItem) itm.getCore().getExpr("origin")).getValue(),
                    ((Item.ArithItem) itm.getCore().getExpr("horizon")).getValue());

            // For each pulse the atoms starting at that pulse
            Map<InfRational, Collection<Atom>> starting_values = new HashMap<>(atoms.size());
            // For each pulse the atoms ending at that pulse
            Map<InfRational, Collection<Atom>> ending_values = new HashMap<>(atoms.size());
            // The pulses of the timeline
            Set<InfRational> c_pulses = new TreeSet<>();
            c_pulses.add(sv.origin);
            c_pulses.add(sv.horizon);

            for (Atom atom : atoms) {
                InfRational start_pulse = ((Item.ArithItem) atom.getExpr("start")).getValue();
                InfRational end_pulse = ((Item.ArithItem) atom.getExpr("end")).getValue();
                c_pulses.add(start_pulse);
                c_pulses.add(end_pulse);
                if (!starting_values.containsKey(start_pulse))
                    starting_values.put(start_pulse, new ArrayList<>(atoms.size()));
                starting_values.get(start_pulse).add(atom);
                if (!ending_values.containsKey(end_pulse))
                    ending_values.put(end_pulse, new ArrayList<>(atoms.size()));
                ending_values.get(end_pulse).add(atom);
            }

            InfRational[] c_pulses_array = c_pulses.toArray(new InfRational[c_pulses.size()]);

            // Push values to timeline according to pulses...
            List<Atom> overlapping_formulas = new ArrayList<>(atoms.size());
            if (starting_values.containsKey(c_pulses_array[0]))
                overlapping_formulas.addAll(starting_values.get(c_pulses_array[0]));
            if (ending_values.containsKey(c_pulses_array[0]))
                overlapping_formulas.removeAll(ending_values.get(c_pulses_array[0]));
            for (int i = 1; i < c_pulses_array.length; i++) {
                sv.addValue(c_pulses_array[i - 1], c_pulses_array[i], new ArrayList<>(overlapping_formulas));
                if (starting_values.containsKey(c_pulses_array[i]))
                    overlapping_formulas.addAll(starting_values.get(c_pulses_array[i]));
                if (ending_values.containsKey(c_pulses_array[i]))
                    overlapping_formulas.removeAll(ending_values.get(c_pulses_array[i]));
            }

            return sv;
        }
    }
}