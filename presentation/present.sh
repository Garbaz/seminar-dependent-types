#/bin/bash

# trap 'kill $BGPID; exit' INT

# { while true;do
#    ~/.scripts_menu/huion_settings_pdfpc.sh
#    sleep 10
# done } &
~/.scripts_menu/huion_settings_pdfpc.sh
pdfpc -X ~/.scripts_menu/huion_settings_pdfpc.sh presentation.pdf
# pdfpc -C presentation.pdf

# kill $!

# echo "$(ps -s $$ -o pid=)"
