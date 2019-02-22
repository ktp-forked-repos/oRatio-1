package it.cnr.istc.oratio.timelines;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import it.cnr.istc.oratio.riddle.Atom;
import it.cnr.istc.oratio.riddle.InfRational;
import it.cnr.istc.oratio.riddle.Item;

/**
 * PropositionalAgent
 */
public class PropositionalAgent implements Timeline<PropositionalAgent.Action> {

    public static TimelineBuilder BUILDER = new PropositionalAgentBuilder();

    private final InfRational origin, horizon;
    private final List<Action> values = new ArrayList<>();

    private PropositionalAgent(final InfRational origin, final InfRational horizon) {
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

    private void addValue(final InfRational from, final InfRational to, final Atom atom) {
        values.add(new Action(from, to, atom));
    }

    @Override
    public List<Action> getValues() {
        return Collections.unmodifiableList(values);
    }

    public class Action implements TimelineValue {

        private final InfRational from, to;
        private final Atom atom;

        private Action(final InfRational from, final InfRational to, final Atom atom) {
            this.from = from;
            this.to = to;
            this.atom = atom;
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
            return Arrays.asList(atom);
        }
    }

    private static class PropositionalAgentBuilder implements TimelineBuilder {

        @Override
        public PropositionalAgent build(Item itm, Collection<Atom> atoms) {
            PropositionalAgent pa = new PropositionalAgent(
                    ((Item.ArithItem) itm.getCore().getExpr("origin")).getValue(),
                    ((Item.ArithItem) itm.getCore().getExpr("horizon")).getValue());

            List<Atom> c_atoms = new ArrayList<>(atoms);
            Collections.sort(c_atoms, (Atom a0, Atom a1) -> (((Item.ArithItem) a0.getExpr("start")).getValue())
                    .compareTo(((Item.ArithItem) a1.getExpr("start")).getValue()));

            for (Atom atm : c_atoms)
                pa.addValue(((Item.ArithItem) atm.getExpr("start")).getValue(),
                        ((Item.ArithItem) atm.getExpr("end")).getValue(), atm);
            return pa;
        }
    }
}