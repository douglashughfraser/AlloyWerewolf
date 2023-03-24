enum Status {
	Alive,
	Dead
}
one var sig Narrator {
	var lynched: set Villager,
}{
	all villager: Villager {
		lynched_this_round[villager] iff villager in lynched
	}
}

some var sig Villager {
	var status: Status,
	var lynch_vote: lone Villager,
	var threats: set Villager,
	var lynch_votes: Int
}{
	(game_end[] or status = Dead or killed_this_round[this]) implies{
		no lynch_vote 
		no threats
	} else one lynch_vote
	
	this not in lynch_vote

	dead_next_round[this] implies status' = Dead else status' = Alive

	lynch_votes = #threats
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

var sig Seer extends Villager {
	var checking: lone Villager,
	var trusted: set Villager,
	var busted: set Villager
}{
	{	
		// Don't need to check which team we're on...
		this not in checking
		this not in busted
	
		// Retain previous information
		trusted in trusted'
		busted in busted'
	
		// Add checked players to known team lists
		checking in Werewolf implies{
			checking in busted
		}else{
			checking in trusted
		}
	
		// Never vote for known teammates
		lynch_vote not in trusted

	} until game_end[] or status = Dead or killed_this_round[this]

	(game_end[] or status = Dead or killed_this_round[this]) implies{
		no checking
		busted = busted'
		trusted = trusted'
	}
}

fact round {
	{	
		// All werewolves vote for the same, alive, Villager
		one victim: Villager | all ww: Werewolf {
			ww.kill_vote = victim
			victim.status = Alive
		}
		
		// Lynch vote bi-implicatoin, needed to count votes. All lynch votes must be for living villagers.
		all voter, threatened: Villager {
			voter in threatened.threats iff threatened in voter.lynch_vote
			voter.lynch_vote = threatened implies not killed_this_round[threatened]
			voter.lynch_vote = threatened implies threatened.status = Alive
		}

		// Seer behaviours
		all seer: Seer {
			not seer.status = Dead or killed_this_round[seer] implies {

				// Existence of an unknown player that is alive, implies that the seer is checking someone
				some villager: Villager - (seer.trusted + seer.busted) |
					(villager.status = Alive) implies {
						seer.checking[status] = Alive
					}
/*
				// Seer only checks living players
				seer.checking[status] = Alive
	
				//Seer always votes for a known enemy *if they're alive*
				all buster: seer.busted |
					buster[status] = Alive implies seer.lynch_vote in seer.busted
*/
			}
		}

	} until game_end[]
}

pred dead_next_round[villager: Villager] {
	// Villagers are dead next round if they're already dead, or have been killed this round
	villager.status = Dead or
	killed_this_round[villager] or
	lynched_this_round[villager]
}

pred killed_this_round[villager: Villager] {
	// Villager are killed this round if the werewolves voted for them
	some ww: Werewolf { 
		ww.kill_vote = villager
	}
}

pred lynched_this_round[villager: Villager] {
	// No other Villager recieved more lynch votes than them
	all other_villager : Villager - villager {
		villager.lynch_votes > other_villager.lynch_votes
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
	#Werewolf = 2
	#Villager = 8 // 1 Werewolf wins 100% in three player games
	#Seer = 1

	always Werewolf' = Werewolf
	always Villager' = Villager
	always Seer' = Seer

	all p: Villager {
		p.status = Alive
	}

	all seer: Seer {
		seer.checking in Werewolf implies {
			seer.trusted = seer
			seer.busted = seer.checking
		} else {
			seer.trusted = seer + seer.checking
			no seer.busted
		}
	}

}

pred close_game[] {
	// Some werewolves die
	eventually some ww: Werewolf |
		ww.status = Dead

	// Some werewolves are lynched
	eventually some ww: Werewolf | lynched_this_round[ww]

	// Some villagers are lynched
	eventually some villager: Villager | lynched_this_round[villager]
}

//fun still_alive[] : set Villager {{villager: Villager | villager.status = Alive}}

run show{
	init[]
	
	one narrator: Narrator |
		narrator.lynched not in Werewolf

	some ww: Werewolf |
		ww.kill_vote not in Seer

	//eventually werewolf_win[]
	//close_game[]
} for 15 but 5 Int, 1..10 steps
