for loop in 1 2 3 4 5 6 7 8 9
do
	java -jar U4T3.jar dump -s "R00$loop.mdj" -n Model -t UMLModel > "$loop.txt"
	java -jar U4T3.jar dump -s "R00$loop.mdj" -n Model1 -t UMLModel >> "$loop.txt"
	java -jar U4T3.jar dump -s "R00$loop.mdj" -n StateMachine1 -t UMLStateMachine >> "$loop.txt"
	java -jar U4T3.jar dump -s "R00$loop.mdj" -n Collaboration1 -t UMLCollaboration >> "$loop.txt"
	java -jar U4T3.jar dump -s "R00$loop.mdj" -n Collaboration2 -t UMLCollaboration >> "$loop.txt"
	echo -e "END_OF_MODEL\n" >> "$loop.txt"
done
