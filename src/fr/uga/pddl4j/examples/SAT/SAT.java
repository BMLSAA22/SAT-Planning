
package fr.uga.pddl4j.examples.sat;
// import fr.uga.pddl4j.problem.Fact;
import fr.uga.pddl4j.heuristics.state.StateHeuristic;
import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.parser.RequireKey;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.planners.Planner;
import fr.uga.pddl4j.planners.PlannerConfiguration;
import fr.uga.pddl4j.planners.ProblemNotSupportedException;
import fr.uga.pddl4j.planners.SearchStrategy;
import fr.uga.pddl4j.planners.statespace.search.StateSpaceSearch;
import fr.uga.pddl4j.problem.DefaultProblem;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.State;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.ConditionalEffect;
import fr.uga.pddl4j.planners.statespace.HSP;
import fr.uga.pddl4j.parser.Parser;
import fr.uga.pddl4j.util.BitSet;
import fr.uga.pddl4j.util.BitVector;
import  fr.uga.pddl4j.problem.operator.AbstractFluentDescription;
import fr.uga.pddl4j.problem.operator.ConditionalEffect;
import fr.uga.pddl4j.planners.InvalidConfigurationException;
import fr.uga.pddl4j.planners.LogLevel;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import picocli.CommandLine;

import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.parser.ErrorManager;
import fr.uga.pddl4j.parser.Message;
import fr.uga.pddl4j.parser.Parser;
import fr.uga.pddl4j.problem.DefaultProblem;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;

import java.io.FileNotFoundException;


import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.TimeoutException;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ISolver;
// import org.sat4j.core.SolverFactory;
// import org.sat4j.specs.ISolver;
// import org.sat4j.specs.IProblem;
// import org.sat4j.specs.TimeoutException;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Set;



@CommandLine.Command(name = "SAT",
    version = "ASP 1.0",
    description = "Solves a specified planning problem using A* search strategy.",
    sortOptions = false,
    mixinStandardHelpOptions = true,
    headerHeading = "Usage:%n",
    synopsisHeading = "%n",
    descriptionHeading = "%nDescription:%n%n",
    parameterListHeading = "%nParameters:%n",
    optionListHeading = "%nOptions:%n")
public class SAT extends AbstractPlanner {

    /**
     * The class logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(SAT.class.getName());

  

    public SAT() {
        this(SAT.getDefaultConfiguration());
    }

    /**
     * Creates a new A* search planner with a specified configuration.
     *
     * @param configuration the configuration of the planner.
     */
    public SAT(final PlannerConfiguration configuration) {
        super();
        this.setConfiguration(configuration);
    }

    /**
     * Instantiates the planning problem from a parsed problem.
     *
     * @param problem the problem to instantiate.
     * @return the instantiated planning problem or null if the problem cannot be instantiated.
     */
    @Override
    public Problem instantiate(DefaultParsedProblem problem) {
        final Problem pb = new DefaultProblem(problem);
        pb.instantiate();
        return pb;
    }


private static void encodeState(ISolver solver, int[][] fluentVars, BitSet initialState, int timeStep , boolean includeAll) throws ContradictionException  {
    
    for (int f = 0; f < fluentVars.length; f++) {
            VecInt clause = new VecInt();   
        
        if (initialState.get(f)) {
            // Fluent f is true
            int fluentVar = fluentVars[f][timeStep];
            clause.push(fluentVar);
            solver.addClause(clause); // Fluent is true
        }
        else if(includeAll){
            int fluentVar = fluentVars[f][timeStep];
            clause.push(-fluentVar);
            solver.addClause(clause);
            // System.out.println(fluentVar);
        }
        
        
    }
    // System.out.println("encoded ended");
    
}







public static void encodeFluentActionImplications(ISolver solver, int[][] fluentVars, int[][] actionVars,Problem problem, int timeStep ) throws ContradictionException {
    int numFluents = fluentVars.length;
    List<Action> actions=problem.getActions();

    for (int fluentIndex = 0; fluentIndex < numFluents; fluentIndex++) {
        int fluentVarCurrent = fluentVars[fluentIndex][timeStep];
        int fluentVarNext = fluentVars[fluentIndex][ timeStep + 1];
        
        // Collect action variables that have the fluent in their positive effects
        VecInt positiveActionVars = new VecInt();
        VecInt negativeActionVars = new VecInt();
        for (int a = 0; a < actionVars.length; a++) {
            Action action = actions.get(a); 
            List<ConditionalEffect> conditionalEffects = action.getConditionalEffects();
            for (ConditionalEffect condEffect : conditionalEffects) {
            // The condition fluents must be true for the effect to apply
            BitVector conditionFluents = condEffect.getEffect().getPositiveFluents();
            BitVector NegativeconditionFluents = condEffect.getEffect().getNegativeFluents();

            
            if (conditionFluents.get(fluentIndex)) {
                int actionVar = actionVars[a][timeStep];
                positiveActionVars.push(actionVar);
            }

            if (NegativeconditionFluents.get(fluentIndex)) {
                int actionVar = actionVars[a][timeStep];
                negativeActionVars.push(actionVar);
            }
            }   
        }
        


        // Encode: (¬f(i) ∧ f(i+1)) → (action_1(i) ∨ action_2(i) ∨ ... ∨ action_n(i))
        VecInt positiveEffectsClause = new VecInt();
        positiveEffectsClause.push(fluentVarCurrent); // ¬f(i)
        positiveEffectsClause.push(-fluentVarNext);     // f(i+1)
        positiveEffectsClause.pushAll(positiveActionVars);// action(i)


       
        solver.addClause(positiveEffectsClause);
        
    
        // System.out.println(positiveEffectsClause);

        // // Encode: (f(i) ∧ ¬f(i+1)) → (action_1(i) ∨ action_2(i) ∨ ... ∨ action_n(i))
        VecInt negativeEffectsClause = new VecInt();
        negativeEffectsClause.push(-fluentVarCurrent);  // f(i)
        negativeEffectsClause.push(fluentVarNext);   // ¬f(i+1)
        negativeEffectsClause.pushAll(negativeActionVars);
        
        solver.addClause(negativeEffectsClause);


       
        // System.out.println(negativeEffectsClause);
        // solver.addClause(negativeEffectsClause);


        if (negativeEffectsClause.size()<3  && positiveEffectsClause.size()<3){
            solver.addClause(new VecInt(new int[] {fluentVarNext, -fluentVarCurrent}));

            // Clause 2: b or not a -> represented as (2, -1)
            solver.addClause(new VecInt(new int[] {-fluentVarNext, fluentVarCurrent}));


        }


    }
}









private static void encodeAction(ISolver solver, int[][] actionVars, int[][] fluentVars, Problem problem, int timeStep) throws ContradictionException {
    VecInt atLeastOneActionClause = new VecInt(); // For at least one action at each time step
    
    for (int a = 0; a < actionVars.length; a++) {
        Action action = problem.getActions().get(a);
         // Get the action from the problem
        atLeastOneActionClause.push(actionVars[a][timeStep]);

        // Handle preconditions (not(action) OR precondition)
        // Action is not applied

        BitVector positivePreconditions = action.getPrecondition().getPositiveFluents();
        for (int f = 0; f < positivePreconditions.size(); f++) {
            VecInt preconditionClause = new VecInt();
            preconditionClause.push(-actionVars[a][timeStep]);
            if (positivePreconditions.get(f)) {
                preconditionClause.push(fluentVars[f][timeStep]);
                solver.addClause(preconditionClause); // Fluent f must be true
            }
        }

        BitVector negativePreconditions = action.getPrecondition().getNegativeFluents();
        for (int f = 0; f < negativePreconditions.size(); f++) {
            VecInt preconditionClause = new VecInt();
            preconditionClause.push(-actionVars[a][timeStep]);
            if (negativePreconditions.get(f)) {
                preconditionClause.push(-fluentVars[f][timeStep]);
                solver.addClause(preconditionClause);  // Fluent f must be false
            }
        }

        // Handle effects (not(action) OR effect(timeStep+1))
        List<ConditionalEffect> conditionalEffects = action.getConditionalEffects();
        for (ConditionalEffect condEffect : conditionalEffects) {
            // Handle conditional effects

            // Condition fluents must be true for the effect to apply
            BitVector conditionFluents = condEffect.getCondition().getPositiveFluents();
            BitVector negativeConditionFluents = condEffect.getCondition().getNegativeFluents();
            BitVector effectFluents = condEffect.getEffect().getPositiveFluents();
            BitVector negativeEffects = condEffect.getEffect().getNegativeFluents();


            // Loop over all fluents in the condition and effect

            for (int f = 0; f < effectFluents.size(); f++) {
                if (effectFluents.get(f)) {
                    VecInt effectClause = new VecInt();
                    effectClause.push(-actionVars[a][timeStep]); // ¬action(t)
                    
                    // Add all condition fluents to the clause (if they are part of the condition)
                    for (int c = 0; c < conditionFluents.size(); c++) {
                        if (conditionFluents.get(c)) {
                            
                            effectClause.push(-fluentVars[c][timeStep]); // ¬condition(t)
                        }
                    }
                    // Finally, the effect fluent at t+1
                    effectClause.push(fluentVars[f][timeStep + 1]); // effect(t+1)
                    solver.addClause(effectClause); // Add the clause to the solver
                    // System.out.println("Adding conditional effect clause: " + effectClause);
                }
            }


            // Handle negative conditional effects (effects that must be false at t+1)
            for (int f = 0; f < negativeEffects.size(); f++) {
                if (negativeEffects.get(f)) {
                    VecInt effectClause = new VecInt();
                    effectClause.push(-actionVars[a][timeStep]); // ¬action(t)
                    
                    // Add all condition fluents to the clause (if they are part of the condition)
                    for (int c = 0; c < conditionFluents.size(); c++) {
                        if (conditionFluents.get(c)) {
                            effectClause.push(-fluentVars[c][timeStep]);// ¬condition(t)
                            solver.addClause(effectClause); 
                        }
                    }

                    // Add negative fluent effect at t+1
                    effectClause.push(-fluentVars[f][timeStep + 1]); // ¬effect(t+1)
                    solver.addClause(effectClause); // Add the clause to the solver
                    // System.out.println("Adding negative conditional effect clause: " + effectClause);
                }
            }
        }

        // Ensure at least one action is applied at this time step
        
        // Ensure mutual exclusion (at most one action is applied at this time step)
        for (int i = 0; i < actionVars.length; i++) {
            for (int j = i + 1; j < actionVars.length; j++) {
                VecInt atMostOneActionClause = new VecInt();
                atMostOneActionClause.push(-actionVars[i][timeStep]); // ¬action_i
                atMostOneActionClause.push(-actionVars[j][timeStep]);
                
                 // ¬action_j
                solver.addClause(atMostOneActionClause); // ¬action_i OR ¬action_j
            }
        }
    }
    solver.addClause(atLeastOneActionClause);

}


// private Plan extractPlan(int[] model, int[][] actionVars, int timeHorizon, Problem problem) {
//     Plan plan = new SequentialPlan();
    
//     // Loop through each time step
//     for (int t = 0; t < timeHorizon; t++) {
//         for (int a = 0; a < actionVars.length; a++) {
//             // Check if the action at time t is true in the model
//             int actionVar = actionVars[a][t];
//             if (model[Math.abs(actionVar) - 1] > 0) {  // Variable is true in the model
//                 Action action = problem.getActions().get(a);
//                 plan.add(t,action);
//             }
//         }
//     }
//     return plan;
// }
    /**
     * Search a solution plan to a specified domain and problem using A*.
     *
     * @param problem the problem to solve.
     * @return the plan found or null if no plan was found.
     */
    @Override
    public Plan solve(final Problem problem) {



        for (int timeHorizon = 3; timeHorizon<25 ; timeHorizon++) {

        ISolver solver = SolverFactory.newDefault();
        

        int numFluents = problem.getFluents().size(); // Replace with actual number of fluents
        int numActions = problem.getActions().size();// Replace with actual number of actions

        
      

//         // Total number of variables
        int totalVariables = (numFluents + numActions) * timeHorizon;
        solver.newVar(totalVariables);


        int[][] fluentVars = new int[numFluents][timeHorizon];
        int[][] actionVars = new int[numActions][timeHorizon];

        for (int f = 0; f < numFluents; f++) {
            for (int t = 0; t < timeHorizon; t++) {
                fluentVars[f][t] = f * timeHorizon + t + 1; // Variable indices are 1-based
            }
        }

        // Create action variables
        for (int a = 0; a < numActions; a++) {
            for (int t = 0; t < timeHorizon; t++) {
                actionVars[a][t] = (numFluents * timeHorizon) + a * timeHorizon + t + 1; // Variable indices are 1-based
            }
        }

        State initialState =new State( problem.getInitialState());
        State goalState =new State( problem.getGoal());


        try {
            VecInt clause = new VecInt();

            encodeState(solver, fluentVars, initialState, 0 , true);
            encodeState(solver, fluentVars, goalState, timeHorizon -1 , false);
            for (int t = 0; t < timeHorizon -1; t++) {
                encodeAction(solver, actionVars, fluentVars, problem, t);
                encodeFluentActionImplications(solver, fluentVars , actionVars, problem, t);
                }

            if (solver.isSatisfiable()) {
                // Extract the solution
                int[] model = solver.model();
                System.out.println("Satisfiable solution found:");
                // Print the rest of the model if necessary (e.g., fluents)
                Plan plan = new SequentialPlan();
                
                for (int i = 0; i < model.length; i++) {
                    if (model[i] > 0) {
                    int vrbl = Math.abs(model[i]);
                    // Loop over actions to identify the one matching the current variable
                    for (int a = 0; a < numActions; a++) {
                        for (int t = 0; t < timeHorizon - 1; t++) {
                            if (actionVars[a][t] == vrbl) {
                            // Get the action and its preconditions/effects
                            Action action = problem.getActions().get(a);
                            
                            plan.add(0, action);
                            System.out.println("plan size" + plan.size() + "plan size");

                            System.out.println("\nTime step: " + t);
                            StringBuilder result = new StringBuilder();
                            for (int k = 0; k< action.getParameters().length; k++) {
                                result.append(action.getParameters()[k]);
                                if (k < action.getParameters().length - 1) {
                                    result.append(", ");
                                }
                            }
                          

                            // Print the preconditions
                            System.out.println("Preconditions:");
                            BitVector preconditions = action.getPrecondition().getPositiveFluents();
                            for (int f = 0; f < preconditions.size(); f++) {
                                if (preconditions.get(f)) {
                                    System.out.println("Fluent " + f + " must be true. " + fluentVars[f][t]);
                                }}
                             BitVector npreconditions = action.getPrecondition().getNegativeFluents();
                            for (int f = 0; f < npreconditions.size(); f++) {
                                if (npreconditions.get(f)) {
                                    System.out.println("Fluent " + f + " must be false.");
                                }
                             }

                            System.out.println("Effects:");
                            List<ConditionalEffect> conditionalEffects = action.getConditionalEffects();
                            for (ConditionalEffect condEffect : conditionalEffects) {
                            // The condition fluents must be true for the effect to apply
                            BitVector conditionFluents = condEffect.getEffect().getPositiveFluents();
                            BitVector NegativeconditionFluents = condEffect.getEffect().getNegativeFluents(); 
                            }
                }
            }
        }
        
        // Now, check if this variable corresponds to a fluent (for state printing)
        for (int f = 0; f < numFluents; f++) {
            for (int t = 0; t < timeHorizon; t++) {
                if (fluentVars[f][t] == vrbl) {
                    // Print the fluent state at this time step
                    System.out.println("At time " + t + ": Fluent " + f + " = true " + vrbl);
                }
            }
        }
    }
}
    System.out.println("found plan " + plan.size());
    // break;
    return plan;
    }

else {
                System.out.println("No solution found");
            }
        } catch (Exception e) {
            System.err.println(e);

        }
        }






        return null;
        // // Creates the A* search strategy
        // StateSpaceSearch search = StateSpaceSearch.getInstance(SearchStrategy.Name.ASTAR,
        //     this.getHeuristic(), this.getHeuristicWeight(), this.getTimeout());
        // LOGGER.info("* Starting A* search \n");
        // // Search a solution
        // Plan plan = search.searchPlan(problem);
        // // If a plan is found update the statistics of the planner and log search information
        // if (plan != null) {
        //     LOGGER.info("* A* search succeeded\n");
        //     this.getStatistics().setTimeToSearch(search.getSearchingTime());
        //     this.getStatistics().setMemoryUsedToSearch(search.getMemoryUsed());
        // } else {
        //     LOGGER.info("* A* search failed\n");
        // }
        // // Return the plan found or null if the search fails.
        // return plan;
    }

    /**
     * Checks the planner configuration and returns if the configuration is valid.
     * A configuration is valid if (1) the domain and the problem files exist and
     * can be read, (2) the timeout is greater than 0, (3) the weight of the
     * heuristic is greater than 0 and (4) the heuristic is a not null.
     *
     * @return <code>true</code> if the configuration is valid <code>false</code> otherwise.
     */


  
    public boolean hasValidConfiguration() {
        return super.hasValidConfiguration();
    }

    /**
     * This method return the default arguments of the planner.
     *
     * @return the default arguments of the planner.
     * @see PlannerConfiguration
     */
    public static PlannerConfiguration getDefaultConfiguration() {
        PlannerConfiguration config = Planner.getDefaultConfiguration();
        return config;
    }

    /**
     * Returns the configuration of the planner.
     *
     * @return the configuration of the planner.
     */
    @Override
    public PlannerConfiguration getConfiguration() {
        final PlannerConfiguration config = super.getConfiguration();
        return config;
    }

    /**
     * Sets the configuration of the planner. If a planner setting is not defined in
     * the specified configuration, the setting is initialized with its default value.
     *
     * @param configuration the configuration to set.
     */
    @Override
    public void setConfiguration(final PlannerConfiguration configuration) {
        super.setConfiguration(configuration);
    }

    /**
     * The main method of the <code>SAT</code> planner.
     *
     * @param args the arguments of the command line.
     */
    public static void main(String[] args) {
        try {
            final SAT planner = new SAT();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }



        

    }


    @Override
    public boolean isSupported(Problem problem) {
        return (problem.getRequirements().contains(RequireKey.ACTION_COSTS)
            || problem.getRequirements().contains(RequireKey.CONSTRAINTS)
            || problem.getRequirements().contains(RequireKey.CONTINOUS_EFFECTS)
            || problem.getRequirements().contains(RequireKey.DERIVED_PREDICATES)
            || problem.getRequirements().contains(RequireKey.DURATIVE_ACTIONS)
            || problem.getRequirements().contains(RequireKey.DURATION_INEQUALITIES)
            || problem.getRequirements().contains(RequireKey.FLUENTS)
            || problem.getRequirements().contains(RequireKey.GOAL_UTILITIES)
            || problem.getRequirements().contains(RequireKey.METHOD_CONSTRAINTS)
            || problem.getRequirements().contains(RequireKey.NUMERIC_FLUENTS)
            || problem.getRequirements().contains(RequireKey.OBJECT_FLUENTS)
            || problem.getRequirements().contains(RequireKey.PREFERENCES)
            || problem.getRequirements().contains(RequireKey.TIMED_INITIAL_LITERALS)
            || problem.getRequirements().contains(RequireKey.HIERARCHY))
            ? false : true;
    }
}