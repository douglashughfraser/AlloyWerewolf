enum Status {
	Alive,
	Dead
}

some var sig Player {
	var status: Status
}{
	dead_next_round[this] implies status' = Dead else status' = Alive
}

var sig Werewolf extends Player {
	var kill_vote: lone Player
}{
	// Players never vote to kill themselves
	kill_vote not in Werewolf
}

fact round {
	{
		// All werewolves vote for the same, alive, player
		one victim: Player | all ww: Werewolf {
			ww.kill_vote = victim
			victim.status = Alive
		}
	} until game_end[]
}

pred dead_next_round[player: Player] {
	killed_this_round[player] or
	player.status = Dead
}

pred killed_this_round[player: Player] {
	some ww: Werewolf { 
		ww.kill_vote = player
	}
}

pred game_end[] {
	(all ww: Werewolf |
		ww.status = Dead
	) or (
	all villager: Player - Werewolf |
		villager.status = Dead
	)
}

pred init[]{
	#Werewolf > 0
	#Player > 0
	#(Player - Werewolf) > #Werewolf

	always Werewolf' = Werewolf
	always Player' = Player

	all p: Player {
		p.status = Alive
	}
}

run show{
	init[]
} for 6 Player, 1..15 steps
