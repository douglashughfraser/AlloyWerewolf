enum Status {
	Alive,
	Dead
}
one var sig Narrator {
	var executed: set Villager,
	var werewolf_kill: set Villager
}{
	all villager: Villager {
		executed_this_round[villager] iff villager in executed
	}

	all villager: Villager, ww: Werewolf {
		villager in werewolf_kill iff ww.kill_vote = villager
	}
}

some var sig Villager {
	var status: Status,
	var execute_vote: lone Villager,
	var threats: set Villager,
	var execute_votes: Int
}{
	(game_end[] or status = Dead or killed_this_round[this]) implies{
		no execute_vote 
		no threats
	} else one execute_vote
	
	this not in execute_vote

	dead_next_round[this] implies status' = Dead else status' = Alive

	execute_votes = #threats
}

var sig Werewolf extends Villager {
	var kill_vote: lone Villager
}{
	// Villagers never vote to kill themselves
	this not in kill_vote

	(game_end[] or status = Dead) implies{
		no kill_vote 
	} else one kill_vote
}

fact round {
	{	
		// All werewolves vote for the same, alive, Villager
		one victim: Villager | all ww: Werewolf {
			ww.kill_vote = victim
			victim.status = Alive
		}
		
		// execute vote bi-implicatoin, needed to count votes. All execute votes must be for living villagers.
		all voter, threatened: Villager {
			voter in threatened.threats iff threatened in voter.execute_vote
			voter.execute_vote = threatened implies not killed_this_round[threatened]
			voter.execute_vote = threatened implies threatened.status = Alive
		}
	} until game_end[]
}

pred dead_next_round[villager: Villager] {
	// Villagers are dead next round if they're already dead, or have been killed this round
	villager.status = Dead or
	killed_this_round[villager] or
	executed_this_round[villager]
}

pred killed_this_round[villager: Villager] {
	// Villager are killed this round if the werewolves voted for them
	some ww: Werewolf { 
		ww.kill_vote = villager
	}
}

pred executed_this_round[villager: Villager] {
	// No other Villager recieved more execute votes than them
	all other_villager : Villager - villager {
		villager.execute_votes > other_villager.execute_votes
	}
}

pred game_end[] {
	village_win[] or werewolf_win[]
	//or #(all ww: Werewolf {ww.status = Alive}) >= #(all villager: Villager {villager.status = Alive})
}

pred village_win[] {
	all ww: Werewolf |
		ww.status = Dead
}

pred werewolf_win[] {
	all villager: Villager - Werewolf {
		villager.status = Dead 
	}//) or (#(Werewolf & still_alive[]) > #((Villager - Werewolf) & still_alive[]))
}

pred init[]{
	#Werewolf = 3
	#Villager = 10 // 1 Werewolf wins 100% in three player games

	always Werewolf' = Werewolf
	always Villager' = Villager

	all p: Villager {
		p.status = Alive
	}
}

pred close_game[] {
	// Some werewolves die
	eventually some ww: Werewolf |
		ww.status = Dead

	// Some werewolves are executed
	eventually some ww: Werewolf | executed_this_round[ww]

	// Some villagers are executed
	eventually some villager: Villager | executed_this_round[villager]
}

//fun still_alive[] : set Villager {{villager: Villager | villager.status = Alive}}

run show{
	init[]
	eventually werewolf_win[]
	close_game[]
} for 18 but 10 Int, 1..10 steps
